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
namespace Cell123_high_first_top
private noncomputable def qValues : Fin 2 → ℚ := ![(15562059649518128248733312094092471/5010122273867260946776040999324726025 : ℚ),(290893323061380864622400000000000000/200404890954690437871041639972989041 : ℚ)]
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
    priceLambda 123 p = ((15562059649518128248733312094092471/5010122273867260946776040999324726025 : ℝ)+(290893323061380864622400000000000000/200404890954690437871041639972989041 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell123,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 123 p = ((145513/100000 : ℝ)*(1/1 : ℝ)-((15562059649518128248733312094092471/5010122273867260946776040999324726025 : ℝ)+(290893323061380864622400000000000000/200404890954690437871041639972989041 : ℝ)*p)/p)/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell123,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e104 x = (x 0*(1-x 0))*(aPoint x+priceLambda 123 (x 0)*(HStar (yPoint x)-HStar (aPoint x))+priceTau 123 (x 0)*psiStar (rPoint x)+(cStar-aPoint x-eta (0 : Fin 9)*psiStar (aPoint x))-(cStar)) := by
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
    (hL : lambdaStar (x 0) = priceLambda 123 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 123 (x 0)) :
    (1)*eval e104 x = (x 0*(1-x 0))*(firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_neg (not_le.mpr ha),hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (4791666666666667/5000000000000000 : ℚ) (31/32 : ℚ)) x → eval e104 x ≤ 0)
    (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((4791666666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((31/32 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 123 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 123 p)
    (hkb : ((31/32 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((4791666666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : bStar < a) :
    firstResidual (0 : Fin 9) a p r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxr⟩ := h5 (4791666666666667/5000000000000000 : ℚ) (31/32 : ℚ) bStar p a r hpcell hkb hr.2 hap hcase
  have hax : aPoint x = a := by simpa only [aPoint,rPoint] using hxa
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 123 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 123 (x 0) := by simpa only [hxp] using hT
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
.const (15562059649518128248733312094092471/5010122273867260946776040999324726025 : ℚ),
.const (290893323061380864622400000000000000/200404890954690437871041639972989041 : ℚ),
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
private noncomputable def ssaQVals : Fin 16 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(-2840189/5000000 : ℚ),(113609/200000 : ℚ),(1085/4818 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ),(4818/3733 : ℚ),(145513/100000 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(15562059649518128248733312094092471/5010122273867260946776040999324726025 : ℚ),(290893323061380864622400000000000000/200404890954690437871041639972989041 : ℚ),(-113609/200000 : ℚ)]
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
private noncomputable def denominator : Int := 865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨829307017216805580728101574019466718966188229917363865558084071472109323095039404933120000000,838321223925683843939756665863410909232748302787880656601224791352934400000000000000000000000⟩,⟨0,865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000⟩,⟨0,865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000⟩,⟨0,865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 3 true
private noncomputable def ibox2 : Fin 4 → FixedTape.I := splitI ibox1 2 432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 1 432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 1 108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox5 1 54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 false
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox7 1 27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 false
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox7 1 27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox6 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox10 1 27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 false
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox10 1 27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 true
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox5 1 54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 true
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox13 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox14 1 81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 false
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox14 1 81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 true
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox13 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox17 1 81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 false
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox17 1 81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox4 1 108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 true
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox20 1 162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 false
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox21 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox22 1 135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 false
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox22 1 135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 true
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox21 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox25 1 135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 false
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox25 1 135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 true
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox20 1 162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 true
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox28 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox29 1 189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 false
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox29 1 189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 true
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox28 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox32 1 189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 false
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox32 1 189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 true
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox3 1 216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 true
private noncomputable def ibox36 : Fin 4 → FixedTape.I := splitI ibox35 1 324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 false
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox36 1 270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 false
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox37 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox38 1 243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 false
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox38 1 243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 true
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox37 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox41 1 243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 false
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox41 1 243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 true
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox36 1 270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 true
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox44 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox45 1 297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 false
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox45 1 297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 true
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox44 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox48 1 297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 false
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox48 1 297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 true
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox35 1 324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 true
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox51 1 378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 false
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox52 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox53 1 351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 false
private noncomputable def ibox55 : Fin 4 → FixedTape.I := splitI ibox53 1 351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 true
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox52 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox56 1 351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 false
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox56 1 351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 true
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox51 1 378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 true
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox59 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox61 : Fin 4 → FixedTape.I := splitI ibox60 1 405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 false
private noncomputable def ibox62 : Fin 4 → FixedTape.I := splitI ibox60 1 405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 true
private noncomputable def ibox63 : Fin 4 → FixedTape.I := splitI ibox59 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox64 : Fin 4 → FixedTape.I := splitI ibox63 1 405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 false
private noncomputable def ibox65 : Fin 4 → FixedTape.I := splitI ibox63 1 405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 true
private noncomputable def ibox66 : Fin 4 → FixedTape.I := splitI ibox2 1 432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 true
private noncomputable def ibox67 : Fin 4 → FixedTape.I := splitI ibox66 1 649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 false
private noncomputable def ibox68 : Fin 4 → FixedTape.I := splitI ibox67 1 540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 false
private noncomputable def ibox69 : Fin 4 → FixedTape.I := splitI ibox68 1 486767162279429328739213547920690205360950627425221026413614394979123200000000000000000000000 false
private noncomputable def ibox70 : Fin 4 → FixedTape.I := splitI ibox69 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox71 : Fin 4 → FixedTape.I := splitI ibox70 1 459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 false
private noncomputable def ibox72 : Fin 4 → FixedTape.I := splitI ibox70 1 459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 true
private noncomputable def ibox73 : Fin 4 → FixedTape.I := splitI ibox69 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox74 : Fin 4 → FixedTape.I := splitI ibox73 1 459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 false
private noncomputable def ibox75 : Fin 4 → FixedTape.I := splitI ibox73 1 459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 true
private noncomputable def ibox76 : Fin 4 → FixedTape.I := splitI ibox68 1 486767162279429328739213547920690205360950627425221026413614394979123200000000000000000000000 true
private noncomputable def ibox77 : Fin 4 → FixedTape.I := splitI ibox76 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox78 : Fin 4 → FixedTape.I := splitI ibox77 1 513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 false
private noncomputable def ibox79 : Fin 4 → FixedTape.I := splitI ibox77 1 513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 true
private noncomputable def ibox80 : Fin 4 → FixedTape.I := splitI ibox76 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox81 : Fin 4 → FixedTape.I := splitI ibox80 1 513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 false
private noncomputable def ibox82 : Fin 4 → FixedTape.I := splitI ibox80 1 513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 true
private noncomputable def ibox83 : Fin 4 → FixedTape.I := splitI ibox67 1 540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 true
private noncomputable def ibox84 : Fin 4 → FixedTape.I := splitI ibox83 1 594937642785969179570149891903065806552272989075270143394417593863372800000000000000000000000 false
private noncomputable def ibox85 : Fin 4 → FixedTape.I := splitI ibox84 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox86 : Fin 4 → FixedTape.I := splitI ibox85 1 567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 false
private noncomputable def ibox87 : Fin 4 → FixedTape.I := splitI ibox85 1 567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 true
private noncomputable def ibox88 : Fin 4 → FixedTape.I := splitI ibox84 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox89 : Fin 4 → FixedTape.I := splitI ibox88 1 567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 false
private noncomputable def ibox90 : Fin 4 → FixedTape.I := splitI ibox88 1 567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 true
private noncomputable def ibox91 : Fin 4 → FixedTape.I := splitI ibox83 1 594937642785969179570149891903065806552272989075270143394417593863372800000000000000000000000 true
private noncomputable def ibox92 : Fin 4 → FixedTape.I := splitI ibox91 1 621980262912604142277883977898659706850103579487782422639618393584435200000000000000000000000 false
private noncomputable def ibox93 : Fin 4 → FixedTape.I := splitI ibox92 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox94 : Fin 4 → FixedTape.I := splitI ibox92 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox95 : Fin 4 → FixedTape.I := splitI ibox91 1 621980262912604142277883977898659706850103579487782422639618393584435200000000000000000000000 true
private noncomputable def ibox96 : Fin 4 → FixedTape.I := splitI ibox95 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox97 : Fin 4 → FixedTape.I := splitI ibox95 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox98 : Fin 4 → FixedTape.I := splitI ibox66 1 649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 true
private noncomputable def ibox99 : Fin 4 → FixedTape.I := splitI ibox98 1 757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 false
private noncomputable def ibox100 : Fin 4 → FixedTape.I := splitI ibox99 1 703108123292509030401086235885441407743595350725319260375220792747622400000000000000000000000 false
private noncomputable def ibox101 : Fin 4 → FixedTape.I := splitI ibox100 1 676065503165874067693352149889847507445764760312806981130019993026560000000000000000000000000 false
private noncomputable def ibox102 : Fin 4 → FixedTape.I := splitI ibox101 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox103 : Fin 4 → FixedTape.I := splitI ibox101 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox104 : Fin 4 → FixedTape.I := splitI ibox100 1 676065503165874067693352149889847507445764760312806981130019993026560000000000000000000000000 true
private noncomputable def ibox105 : Fin 4 → FixedTape.I := splitI ibox104 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox106 : Fin 4 → FixedTape.I := splitI ibox104 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox107 : Fin 4 → FixedTape.I := splitI ibox99 1 703108123292509030401086235885441407743595350725319260375220792747622400000000000000000000000 true
private noncomputable def ibox108 : Fin 4 → FixedTape.I := splitI ibox107 1 730150743419143993108820321881035308041425941137831539620421592468684800000000000000000000000 false
private noncomputable def ibox109 : Fin 4 → FixedTape.I := splitI ibox108 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox110 : Fin 4 → FixedTape.I := splitI ibox108 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox111 : Fin 4 → FixedTape.I := splitI ibox107 1 730150743419143993108820321881035308041425941137831539620421592468684800000000000000000000000 true
private noncomputable def ibox112 : Fin 4 → FixedTape.I := splitI ibox111 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox113 : Fin 4 → FixedTape.I := splitI ibox111 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox114 : Fin 4 → FixedTape.I := splitI ibox98 1 757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 true
private noncomputable def ibox115 : Fin 4 → FixedTape.I := splitI ibox114 1 811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 false
private noncomputable def ibox116 : Fin 4 → FixedTape.I := splitI ibox115 1 784235983672413918524288493872223108637087121962856098110823191910809600000000000000000000000 false
private noncomputable def ibox117 : Fin 4 → FixedTape.I := splitI ibox116 1 770714673609096437170421450874426158488171826756599958488222792050278400000000000000000000000 false
private noncomputable def ibox118 : Fin 4 → FixedTape.I := splitI ibox116 1 770714673609096437170421450874426158488171826756599958488222792050278400000000000000000000000 true
private noncomputable def ibox119 : Fin 4 → FixedTape.I := splitI ibox115 1 784235983672413918524288493872223108637087121962856098110823191910809600000000000000000000000 true
private noncomputable def ibox120 : Fin 4 → FixedTape.I := splitI ibox119 1 797757293735731399878155536870020058786002417169112237733423591771340800000000000000000000000 false
private noncomputable def ibox121 : Fin 4 → FixedTape.I := splitI ibox119 1 797757293735731399878155536870020058786002417169112237733423591771340800000000000000000000000 true
private noncomputable def ibox122 : Fin 4 → FixedTape.I := splitI ibox114 1 811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 true
private noncomputable def ibox123 : Fin 4 → FixedTape.I := splitI ibox122 1 838321223925683843939756665863410909232748302787880656601224791352934400000000000000000000000 false
private noncomputable def ibox124 : Fin 4 → FixedTape.I := splitI ibox123 1 824799913862366362585889622865613959083833007581624516978624391492403200000000000000000000000 false
private noncomputable def ibox125 : Fin 4 → FixedTape.I := splitI ibox123 1 824799913862366362585889622865613959083833007581624516978624391492403200000000000000000000000 true
private noncomputable def ibox126 : Fin 4 → FixedTape.I := splitI ibox122 1 838321223925683843939756665863410909232748302787880656601224791352934400000000000000000000000 true
private noncomputable def ibox127 : Fin 4 → FixedTape.I := splitI ibox126 1 851842533989001325293623708861207859381663597994136796223825191213465600000000000000000000000 false
private noncomputable def ibox128 : Fin 4 → FixedTape.I := splitI ibox126 1 851842533989001325293623708861207859381663597994136796223825191213465600000000000000000000000 true
private noncomputable def ibox129 : Fin 4 → FixedTape.I := splitI ibox1 2 432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 true
private noncomputable def ibox130 : Fin 4 → FixedTape.I := splitI ibox129 2 649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 false
private noncomputable def ibox131 : Fin 4 → FixedTape.I := splitI ibox130 1 432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 false
private noncomputable def ibox132 : Fin 4 → FixedTape.I := splitI ibox131 1 216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 false
private noncomputable def ibox133 : Fin 4 → FixedTape.I := splitI ibox132 1 108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 false
private noncomputable def ibox134 : Fin 4 → FixedTape.I := splitI ibox133 1 54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 false
private noncomputable def ibox135 : Fin 4 → FixedTape.I := splitI ibox134 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox136 : Fin 4 → FixedTape.I := splitI ibox135 1 27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 false
private noncomputable def ibox137 : Fin 4 → FixedTape.I := splitI ibox135 1 27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 true
private noncomputable def ibox138 : Fin 4 → FixedTape.I := splitI ibox134 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox139 : Fin 4 → FixedTape.I := splitI ibox138 1 27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 false
private noncomputable def ibox140 : Fin 4 → FixedTape.I := splitI ibox138 1 27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 true
private noncomputable def ibox141 : Fin 4 → FixedTape.I := splitI ibox133 1 54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 true
private noncomputable def ibox142 : Fin 4 → FixedTape.I := splitI ibox141 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox143 : Fin 4 → FixedTape.I := splitI ibox142 1 81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 false
private noncomputable def ibox144 : Fin 4 → FixedTape.I := splitI ibox142 1 81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 true
private noncomputable def ibox145 : Fin 4 → FixedTape.I := splitI ibox141 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox146 : Fin 4 → FixedTape.I := splitI ibox145 1 81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 false
private noncomputable def ibox147 : Fin 4 → FixedTape.I := splitI ibox145 1 81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 true
private noncomputable def ibox148 : Fin 4 → FixedTape.I := splitI ibox132 1 108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 true
private noncomputable def ibox149 : Fin 4 → FixedTape.I := splitI ibox148 1 162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 false
private noncomputable def ibox150 : Fin 4 → FixedTape.I := splitI ibox149 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox151 : Fin 4 → FixedTape.I := splitI ibox150 1 135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 false
private noncomputable def ibox152 : Fin 4 → FixedTape.I := splitI ibox150 1 135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 true
private noncomputable def ibox153 : Fin 4 → FixedTape.I := splitI ibox149 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox154 : Fin 4 → FixedTape.I := splitI ibox153 1 135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 false
private noncomputable def ibox155 : Fin 4 → FixedTape.I := splitI ibox153 1 135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 true
private noncomputable def ibox156 : Fin 4 → FixedTape.I := splitI ibox148 1 162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 true
private noncomputable def ibox157 : Fin 4 → FixedTape.I := splitI ibox156 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox158 : Fin 4 → FixedTape.I := splitI ibox157 1 189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 false
private noncomputable def ibox159 : Fin 4 → FixedTape.I := splitI ibox157 1 189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 true
private noncomputable def ibox160 : Fin 4 → FixedTape.I := splitI ibox156 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox161 : Fin 4 → FixedTape.I := splitI ibox160 1 189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 false
private noncomputable def ibox162 : Fin 4 → FixedTape.I := splitI ibox160 1 189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 true
private noncomputable def ibox163 : Fin 4 → FixedTape.I := splitI ibox131 1 216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 true
private noncomputable def ibox164 : Fin 4 → FixedTape.I := splitI ibox163 1 324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 false
private noncomputable def ibox165 : Fin 4 → FixedTape.I := splitI ibox164 1 270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 false
private noncomputable def ibox166 : Fin 4 → FixedTape.I := splitI ibox165 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox167 : Fin 4 → FixedTape.I := splitI ibox166 1 243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 false
private noncomputable def ibox168 : Fin 4 → FixedTape.I := splitI ibox166 1 243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 true
private noncomputable def ibox169 : Fin 4 → FixedTape.I := splitI ibox165 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox170 : Fin 4 → FixedTape.I := splitI ibox169 1 243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 false
private noncomputable def ibox171 : Fin 4 → FixedTape.I := splitI ibox169 1 243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 true
private noncomputable def ibox172 : Fin 4 → FixedTape.I := splitI ibox164 1 270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 true
private noncomputable def ibox173 : Fin 4 → FixedTape.I := splitI ibox172 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox174 : Fin 4 → FixedTape.I := splitI ibox173 1 297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 false
private noncomputable def ibox175 : Fin 4 → FixedTape.I := splitI ibox173 1 297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 true
private noncomputable def ibox176 : Fin 4 → FixedTape.I := splitI ibox172 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox177 : Fin 4 → FixedTape.I := splitI ibox176 1 297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 false
private noncomputable def ibox178 : Fin 4 → FixedTape.I := splitI ibox176 1 297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 true
private noncomputable def ibox179 : Fin 4 → FixedTape.I := splitI ibox163 1 324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 true
private noncomputable def ibox180 : Fin 4 → FixedTape.I := splitI ibox179 1 378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 false
private noncomputable def ibox181 : Fin 4 → FixedTape.I := splitI ibox180 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox182 : Fin 4 → FixedTape.I := splitI ibox181 1 351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 false
private noncomputable def ibox183 : Fin 4 → FixedTape.I := splitI ibox181 1 351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 true
private noncomputable def ibox184 : Fin 4 → FixedTape.I := splitI ibox180 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox185 : Fin 4 → FixedTape.I := splitI ibox184 1 351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 false
private noncomputable def ibox186 : Fin 4 → FixedTape.I := splitI ibox184 1 351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 true
private noncomputable def ibox187 : Fin 4 → FixedTape.I := splitI ibox179 1 378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 true
private noncomputable def ibox188 : Fin 4 → FixedTape.I := splitI ibox187 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox189 : Fin 4 → FixedTape.I := splitI ibox188 1 405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 false
private noncomputable def ibox190 : Fin 4 → FixedTape.I := splitI ibox188 1 405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 true
private noncomputable def ibox191 : Fin 4 → FixedTape.I := splitI ibox187 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox192 : Fin 4 → FixedTape.I := splitI ibox191 1 405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 false
private noncomputable def ibox193 : Fin 4 → FixedTape.I := splitI ibox191 1 405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 true
private noncomputable def ibox194 : Fin 4 → FixedTape.I := splitI ibox130 1 432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 true
private noncomputable def ibox195 : Fin 4 → FixedTape.I := splitI ibox194 1 649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 false
private noncomputable def ibox196 : Fin 4 → FixedTape.I := splitI ibox195 1 540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 false
private noncomputable def ibox197 : Fin 4 → FixedTape.I := splitI ibox196 1 486767162279429328739213547920690205360950627425221026413614394979123200000000000000000000000 false
private noncomputable def ibox198 : Fin 4 → FixedTape.I := splitI ibox197 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox199 : Fin 4 → FixedTape.I := splitI ibox198 1 459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 false
private noncomputable def ibox200 : Fin 4 → FixedTape.I := splitI ibox198 1 459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 true
private noncomputable def ibox201 : Fin 4 → FixedTape.I := splitI ibox197 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox202 : Fin 4 → FixedTape.I := splitI ibox201 1 459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 false
private noncomputable def ibox203 : Fin 4 → FixedTape.I := splitI ibox201 1 459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 true
private noncomputable def ibox204 : Fin 4 → FixedTape.I := splitI ibox196 1 486767162279429328739213547920690205360950627425221026413614394979123200000000000000000000000 true
private noncomputable def ibox205 : Fin 4 → FixedTape.I := splitI ibox204 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox206 : Fin 4 → FixedTape.I := splitI ibox205 1 513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 false
private noncomputable def ibox207 : Fin 4 → FixedTape.I := splitI ibox205 1 513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 true
private noncomputable def ibox208 : Fin 4 → FixedTape.I := splitI ibox204 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox209 : Fin 4 → FixedTape.I := splitI ibox208 1 513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 false
private noncomputable def ibox210 : Fin 4 → FixedTape.I := splitI ibox208 1 513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 true
private noncomputable def ibox211 : Fin 4 → FixedTape.I := splitI ibox195 1 540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 true
private noncomputable def ibox212 : Fin 4 → FixedTape.I := splitI ibox211 1 594937642785969179570149891903065806552272989075270143394417593863372800000000000000000000000 false
private noncomputable def ibox213 : Fin 4 → FixedTape.I := splitI ibox212 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox214 : Fin 4 → FixedTape.I := splitI ibox213 1 567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 false
private noncomputable def ibox215 : Fin 4 → FixedTape.I := splitI ibox213 1 567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 true
private noncomputable def ibox216 : Fin 4 → FixedTape.I := splitI ibox212 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox217 : Fin 4 → FixedTape.I := splitI ibox216 1 567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 false
private noncomputable def ibox218 : Fin 4 → FixedTape.I := splitI ibox217 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox219 : Fin 4 → FixedTape.I := splitI ibox217 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox220 : Fin 4 → FixedTape.I := splitI ibox216 1 567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 true
private noncomputable def ibox221 : Fin 4 → FixedTape.I := splitI ibox220 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox222 : Fin 4 → FixedTape.I := splitI ibox220 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox223 : Fin 4 → FixedTape.I := splitI ibox211 1 594937642785969179570149891903065806552272989075270143394417593863372800000000000000000000000 true
private noncomputable def ibox224 : Fin 4 → FixedTape.I := splitI ibox223 1 621980262912604142277883977898659706850103579487782422639618393584435200000000000000000000000 false
private noncomputable def ibox225 : Fin 4 → FixedTape.I := splitI ibox224 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox226 : Fin 4 → FixedTape.I := splitI ibox224 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox227 : Fin 4 → FixedTape.I := splitI ibox226 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox228 : Fin 4 → FixedTape.I := splitI ibox226 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox229 : Fin 4 → FixedTape.I := splitI ibox223 1 621980262912604142277883977898659706850103579487782422639618393584435200000000000000000000000 true
private noncomputable def ibox230 : Fin 4 → FixedTape.I := splitI ibox229 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox231 : Fin 4 → FixedTape.I := splitI ibox229 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox232 : Fin 4 → FixedTape.I := splitI ibox194 1 649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 true
private noncomputable def ibox233 : Fin 4 → FixedTape.I := splitI ibox232 1 757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 false
private noncomputable def ibox234 : Fin 4 → FixedTape.I := splitI ibox233 1 703108123292509030401086235885441407743595350725319260375220792747622400000000000000000000000 false
private noncomputable def ibox235 : Fin 4 → FixedTape.I := splitI ibox234 1 676065503165874067693352149889847507445764760312806981130019993026560000000000000000000000000 false
private noncomputable def ibox236 : Fin 4 → FixedTape.I := splitI ibox235 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox237 : Fin 4 → FixedTape.I := splitI ibox235 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox238 : Fin 4 → FixedTape.I := splitI ibox234 1 676065503165874067693352149889847507445764760312806981130019993026560000000000000000000000000 true
private noncomputable def ibox239 : Fin 4 → FixedTape.I := splitI ibox238 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox240 : Fin 4 → FixedTape.I := splitI ibox238 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox241 : Fin 4 → FixedTape.I := splitI ibox233 1 703108123292509030401086235885441407743595350725319260375220792747622400000000000000000000000 true
private noncomputable def ibox242 : Fin 4 → FixedTape.I := splitI ibox241 1 730150743419143993108820321881035308041425941137831539620421592468684800000000000000000000000 false
private noncomputable def ibox243 : Fin 4 → FixedTape.I := splitI ibox242 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox244 : Fin 4 → FixedTape.I := splitI ibox242 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox245 : Fin 4 → FixedTape.I := splitI ibox241 1 730150743419143993108820321881035308041425941137831539620421592468684800000000000000000000000 true
private noncomputable def ibox246 : Fin 4 → FixedTape.I := splitI ibox245 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox247 : Fin 4 → FixedTape.I := splitI ibox245 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox248 : Fin 4 → FixedTape.I := splitI ibox232 1 757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 true
private noncomputable def ibox249 : Fin 4 → FixedTape.I := splitI ibox248 1 811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 false
private noncomputable def ibox250 : Fin 4 → FixedTape.I := splitI ibox249 1 784235983672413918524288493872223108637087121962856098110823191910809600000000000000000000000 false
private noncomputable def ibox251 : Fin 4 → FixedTape.I := splitI ibox250 1 770714673609096437170421450874426158488171826756599958488222792050278400000000000000000000000 false
private noncomputable def ibox252 : Fin 4 → FixedTape.I := splitI ibox250 1 770714673609096437170421450874426158488171826756599958488222792050278400000000000000000000000 true
private noncomputable def ibox253 : Fin 4 → FixedTape.I := splitI ibox249 1 784235983672413918524288493872223108637087121962856098110823191910809600000000000000000000000 true
private noncomputable def ibox254 : Fin 4 → FixedTape.I := splitI ibox253 1 797757293735731399878155536870020058786002417169112237733423591771340800000000000000000000000 false
private noncomputable def ibox255 : Fin 4 → FixedTape.I := splitI ibox253 1 797757293735731399878155536870020058786002417169112237733423591771340800000000000000000000000 true
private noncomputable def ibox256 : Fin 4 → FixedTape.I := splitI ibox248 1 811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 true
private noncomputable def ibox257 : Fin 4 → FixedTape.I := splitI ibox256 1 838321223925683843939756665863410909232748302787880656601224791352934400000000000000000000000 false
private noncomputable def ibox258 : Fin 4 → FixedTape.I := splitI ibox257 1 824799913862366362585889622865613959083833007581624516978624391492403200000000000000000000000 false
private noncomputable def ibox259 : Fin 4 → FixedTape.I := splitI ibox257 1 824799913862366362585889622865613959083833007581624516978624391492403200000000000000000000000 true
private noncomputable def ibox260 : Fin 4 → FixedTape.I := splitI ibox256 1 838321223925683843939756665863410909232748302787880656601224791352934400000000000000000000000 true
private noncomputable def ibox261 : Fin 4 → FixedTape.I := splitI ibox260 1 851842533989001325293623708861207859381663597994136796223825191213465600000000000000000000000 false
private noncomputable def ibox262 : Fin 4 → FixedTape.I := splitI ibox260 1 851842533989001325293623708861207859381663597994136796223825191213465600000000000000000000000 true
private noncomputable def ibox263 : Fin 4 → FixedTape.I := splitI ibox129 2 649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 true
private noncomputable def ibox264 : Fin 4 → FixedTape.I := splitI ibox263 1 432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 false
private noncomputable def ibox265 : Fin 4 → FixedTape.I := splitI ibox264 2 757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 false
private noncomputable def ibox266 : Fin 4 → FixedTape.I := splitI ibox265 1 216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 false
private noncomputable def ibox267 : Fin 4 → FixedTape.I := splitI ibox266 1 108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 false
private noncomputable def ibox268 : Fin 4 → FixedTape.I := splitI ibox267 1 54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 false
private noncomputable def ibox269 : Fin 4 → FixedTape.I := splitI ibox268 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox270 : Fin 4 → FixedTape.I := splitI ibox269 1 27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 false
private noncomputable def ibox271 : Fin 4 → FixedTape.I := splitI ibox269 1 27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 true
private noncomputable def ibox272 : Fin 4 → FixedTape.I := splitI ibox268 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox273 : Fin 4 → FixedTape.I := splitI ibox272 1 27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 false
private noncomputable def ibox274 : Fin 4 → FixedTape.I := splitI ibox272 1 27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 true
private noncomputable def ibox275 : Fin 4 → FixedTape.I := splitI ibox267 1 54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 true
private noncomputable def ibox276 : Fin 4 → FixedTape.I := splitI ibox275 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox277 : Fin 4 → FixedTape.I := splitI ibox276 1 81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 false
private noncomputable def ibox278 : Fin 4 → FixedTape.I := splitI ibox276 1 81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 true
private noncomputable def ibox279 : Fin 4 → FixedTape.I := splitI ibox275 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox280 : Fin 4 → FixedTape.I := splitI ibox279 1 81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 false
private noncomputable def ibox281 : Fin 4 → FixedTape.I := splitI ibox279 1 81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 true
private noncomputable def ibox282 : Fin 4 → FixedTape.I := splitI ibox266 1 108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 true
private noncomputable def ibox283 : Fin 4 → FixedTape.I := splitI ibox282 1 162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 false
private noncomputable def ibox284 : Fin 4 → FixedTape.I := splitI ibox283 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox285 : Fin 4 → FixedTape.I := splitI ibox284 1 135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 false
private noncomputable def ibox286 : Fin 4 → FixedTape.I := splitI ibox284 1 135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 true
private noncomputable def ibox287 : Fin 4 → FixedTape.I := splitI ibox283 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox288 : Fin 4 → FixedTape.I := splitI ibox287 1 135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 false
private noncomputable def ibox289 : Fin 4 → FixedTape.I := splitI ibox287 1 135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 true
private noncomputable def ibox290 : Fin 4 → FixedTape.I := splitI ibox282 1 162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 true
private noncomputable def ibox291 : Fin 4 → FixedTape.I := splitI ibox290 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox292 : Fin 4 → FixedTape.I := splitI ibox291 1 189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 false
private noncomputable def ibox293 : Fin 4 → FixedTape.I := splitI ibox291 1 189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 true
private noncomputable def ibox294 : Fin 4 → FixedTape.I := splitI ibox290 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox295 : Fin 4 → FixedTape.I := splitI ibox294 1 189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 false
private noncomputable def ibox296 : Fin 4 → FixedTape.I := splitI ibox294 1 189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 true
private noncomputable def ibox297 : Fin 4 → FixedTape.I := splitI ibox265 1 216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 true
private noncomputable def ibox298 : Fin 4 → FixedTape.I := splitI ibox297 1 324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 false
private noncomputable def ibox299 : Fin 4 → FixedTape.I := splitI ibox298 1 270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 false
private noncomputable def ibox300 : Fin 4 → FixedTape.I := splitI ibox299 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox301 : Fin 4 → FixedTape.I := splitI ibox300 1 243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 false
private noncomputable def ibox302 : Fin 4 → FixedTape.I := splitI ibox300 1 243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 true
private noncomputable def ibox303 : Fin 4 → FixedTape.I := splitI ibox299 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox304 : Fin 4 → FixedTape.I := splitI ibox303 1 243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 false
private noncomputable def ibox305 : Fin 4 → FixedTape.I := splitI ibox303 1 243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 true
private noncomputable def ibox306 : Fin 4 → FixedTape.I := splitI ibox298 1 270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 true
private noncomputable def ibox307 : Fin 4 → FixedTape.I := splitI ibox306 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox308 : Fin 4 → FixedTape.I := splitI ibox307 1 297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 false
private noncomputable def ibox309 : Fin 4 → FixedTape.I := splitI ibox307 1 297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 true
private noncomputable def ibox310 : Fin 4 → FixedTape.I := splitI ibox306 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox311 : Fin 4 → FixedTape.I := splitI ibox310 1 297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 false
private noncomputable def ibox312 : Fin 4 → FixedTape.I := splitI ibox310 1 297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 true
private noncomputable def ibox313 : Fin 4 → FixedTape.I := splitI ibox297 1 324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 true
private noncomputable def ibox314 : Fin 4 → FixedTape.I := splitI ibox313 1 378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 false
private noncomputable def ibox315 : Fin 4 → FixedTape.I := splitI ibox314 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox316 : Fin 4 → FixedTape.I := splitI ibox315 1 351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 false
private noncomputable def ibox317 : Fin 4 → FixedTape.I := splitI ibox315 1 351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 true
private noncomputable def ibox318 : Fin 4 → FixedTape.I := splitI ibox314 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox319 : Fin 4 → FixedTape.I := splitI ibox318 1 351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 false
private noncomputable def ibox320 : Fin 4 → FixedTape.I := splitI ibox318 1 351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 true
private noncomputable def ibox321 : Fin 4 → FixedTape.I := splitI ibox313 1 378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 true
private noncomputable def ibox322 : Fin 4 → FixedTape.I := splitI ibox321 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox323 : Fin 4 → FixedTape.I := splitI ibox322 1 405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 false
private noncomputable def ibox324 : Fin 4 → FixedTape.I := splitI ibox322 1 405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 true
private noncomputable def ibox325 : Fin 4 → FixedTape.I := splitI ibox321 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox326 : Fin 4 → FixedTape.I := splitI ibox325 1 405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 false
private noncomputable def ibox327 : Fin 4 → FixedTape.I := splitI ibox325 1 405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 true
private noncomputable def ibox328 : Fin 4 → FixedTape.I := splitI ibox264 2 757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 true
private noncomputable def ibox329 : Fin 4 → FixedTape.I := splitI ibox328 2 811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 false
private noncomputable def ibox330 : Fin 4 → FixedTape.I := splitI ibox329 1 216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 false
private noncomputable def ibox331 : Fin 4 → FixedTape.I := splitI ibox330 1 108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 false
private noncomputable def ibox332 : Fin 4 → FixedTape.I := splitI ibox331 1 54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 false
private noncomputable def ibox333 : Fin 4 → FixedTape.I := splitI ibox332 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox334 : Fin 4 → FixedTape.I := splitI ibox333 1 27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 false
private noncomputable def ibox335 : Fin 4 → FixedTape.I := splitI ibox333 1 27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 true
private noncomputable def ibox336 : Fin 4 → FixedTape.I := splitI ibox332 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox337 : Fin 4 → FixedTape.I := splitI ibox336 1 27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 false
private noncomputable def ibox338 : Fin 4 → FixedTape.I := splitI ibox336 1 27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 true
private noncomputable def ibox339 : Fin 4 → FixedTape.I := splitI ibox331 1 54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 true
private noncomputable def ibox340 : Fin 4 → FixedTape.I := splitI ibox339 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox341 : Fin 4 → FixedTape.I := splitI ibox340 1 81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 false
private noncomputable def ibox342 : Fin 4 → FixedTape.I := splitI ibox340 1 81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 true
private noncomputable def ibox343 : Fin 4 → FixedTape.I := splitI ibox339 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox344 : Fin 4 → FixedTape.I := splitI ibox343 1 81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 false
private noncomputable def ibox345 : Fin 4 → FixedTape.I := splitI ibox343 1 81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 true
private noncomputable def ibox346 : Fin 4 → FixedTape.I := splitI ibox330 1 108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 true
private noncomputable def ibox347 : Fin 4 → FixedTape.I := splitI ibox346 1 162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 false
private noncomputable def ibox348 : Fin 4 → FixedTape.I := splitI ibox347 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox349 : Fin 4 → FixedTape.I := splitI ibox348 1 135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 false
private noncomputable def ibox350 : Fin 4 → FixedTape.I := splitI ibox348 1 135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 true
private noncomputable def ibox351 : Fin 4 → FixedTape.I := splitI ibox347 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox352 : Fin 4 → FixedTape.I := splitI ibox351 1 135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 false
private noncomputable def ibox353 : Fin 4 → FixedTape.I := splitI ibox351 1 135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 true
private noncomputable def ibox354 : Fin 4 → FixedTape.I := splitI ibox346 1 162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 true
private noncomputable def ibox355 : Fin 4 → FixedTape.I := splitI ibox354 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox356 : Fin 4 → FixedTape.I := splitI ibox355 1 189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 false
private noncomputable def ibox357 : Fin 4 → FixedTape.I := splitI ibox355 1 189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 true
private noncomputable def ibox358 : Fin 4 → FixedTape.I := splitI ibox354 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox359 : Fin 4 → FixedTape.I := splitI ibox358 1 189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 false
private noncomputable def ibox360 : Fin 4 → FixedTape.I := splitI ibox358 1 189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 true
private noncomputable def ibox361 : Fin 4 → FixedTape.I := splitI ibox329 1 216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 true
private noncomputable def ibox362 : Fin 4 → FixedTape.I := splitI ibox361 1 324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 false
private noncomputable def ibox363 : Fin 4 → FixedTape.I := splitI ibox362 1 270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 false
private noncomputable def ibox364 : Fin 4 → FixedTape.I := splitI ibox363 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox365 : Fin 4 → FixedTape.I := splitI ibox364 1 243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 false
private noncomputable def ibox366 : Fin 4 → FixedTape.I := splitI ibox364 1 243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 true
private noncomputable def ibox367 : Fin 4 → FixedTape.I := splitI ibox363 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox368 : Fin 4 → FixedTape.I := splitI ibox367 1 243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 false
private noncomputable def ibox369 : Fin 4 → FixedTape.I := splitI ibox367 1 243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 true
private noncomputable def ibox370 : Fin 4 → FixedTape.I := splitI ibox362 1 270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 true
private noncomputable def ibox371 : Fin 4 → FixedTape.I := splitI ibox370 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox372 : Fin 4 → FixedTape.I := splitI ibox371 1 297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 false
private noncomputable def ibox373 : Fin 4 → FixedTape.I := splitI ibox371 1 297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 true
private noncomputable def ibox374 : Fin 4 → FixedTape.I := splitI ibox370 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox375 : Fin 4 → FixedTape.I := splitI ibox374 1 297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 false
private noncomputable def ibox376 : Fin 4 → FixedTape.I := splitI ibox374 1 297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 true
private noncomputable def ibox377 : Fin 4 → FixedTape.I := splitI ibox361 1 324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 true
private noncomputable def ibox378 : Fin 4 → FixedTape.I := splitI ibox377 1 378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 false
private noncomputable def ibox379 : Fin 4 → FixedTape.I := splitI ibox378 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox380 : Fin 4 → FixedTape.I := splitI ibox379 1 351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 false
private noncomputable def ibox381 : Fin 4 → FixedTape.I := splitI ibox379 1 351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 true
private noncomputable def ibox382 : Fin 4 → FixedTape.I := splitI ibox378 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox383 : Fin 4 → FixedTape.I := splitI ibox382 1 351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 false
private noncomputable def ibox384 : Fin 4 → FixedTape.I := splitI ibox382 1 351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 true
private noncomputable def ibox385 : Fin 4 → FixedTape.I := splitI ibox377 1 378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 true
private noncomputable def ibox386 : Fin 4 → FixedTape.I := splitI ibox385 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox387 : Fin 4 → FixedTape.I := splitI ibox386 1 405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 false
private noncomputable def ibox388 : Fin 4 → FixedTape.I := splitI ibox386 1 405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 true
private noncomputable def ibox389 : Fin 4 → FixedTape.I := splitI ibox385 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox390 : Fin 4 → FixedTape.I := splitI ibox389 1 405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 false
private noncomputable def ibox391 : Fin 4 → FixedTape.I := splitI ibox389 1 405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 true
private noncomputable def ibox392 : Fin 4 → FixedTape.I := splitI ibox328 2 811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 true
private noncomputable def ibox393 : Fin 4 → FixedTape.I := splitI ibox392 1 216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 false
private noncomputable def ibox394 : Fin 4 → FixedTape.I := splitI ibox393 1 108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 false
private noncomputable def ibox395 : Fin 4 → FixedTape.I := splitI ibox394 1 54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 false
private noncomputable def ibox396 : Fin 4 → FixedTape.I := splitI ibox395 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox397 : Fin 4 → FixedTape.I := splitI ibox396 1 27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 false
private noncomputable def ibox398 : Fin 4 → FixedTape.I := splitI ibox396 1 27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 true
private noncomputable def ibox399 : Fin 4 → FixedTape.I := splitI ibox395 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox400 : Fin 4 → FixedTape.I := splitI ibox399 1 27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 false
private noncomputable def ibox401 : Fin 4 → FixedTape.I := splitI ibox400 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox402 : Fin 4 → FixedTape.I := splitI ibox400 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox403 : Fin 4 → FixedTape.I := splitI ibox399 1 27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 true
private noncomputable def ibox404 : Fin 4 → FixedTape.I := splitI ibox403 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox405 : Fin 4 → FixedTape.I := splitI ibox403 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox406 : Fin 4 → FixedTape.I := splitI ibox394 1 54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 true
private noncomputable def ibox407 : Fin 4 → FixedTape.I := splitI ibox406 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox408 : Fin 4 → FixedTape.I := splitI ibox407 1 81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 false
private noncomputable def ibox409 : Fin 4 → FixedTape.I := splitI ibox407 1 81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 true
private noncomputable def ibox410 : Fin 4 → FixedTape.I := splitI ibox406 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox411 : Fin 4 → FixedTape.I := splitI ibox410 1 81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 false
private noncomputable def ibox412 : Fin 4 → FixedTape.I := splitI ibox411 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox413 : Fin 4 → FixedTape.I := splitI ibox411 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox414 : Fin 4 → FixedTape.I := splitI ibox410 1 81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 true
private noncomputable def ibox415 : Fin 4 → FixedTape.I := splitI ibox414 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox416 : Fin 4 → FixedTape.I := splitI ibox414 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox417 : Fin 4 → FixedTape.I := splitI ibox393 1 108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 true
private noncomputable def ibox418 : Fin 4 → FixedTape.I := splitI ibox417 1 162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 false
private noncomputable def ibox419 : Fin 4 → FixedTape.I := splitI ibox418 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox420 : Fin 4 → FixedTape.I := splitI ibox419 1 135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 false
private noncomputable def ibox421 : Fin 4 → FixedTape.I := splitI ibox419 1 135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 true
private noncomputable def ibox422 : Fin 4 → FixedTape.I := splitI ibox418 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox423 : Fin 4 → FixedTape.I := splitI ibox422 1 135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 false
private noncomputable def ibox424 : Fin 4 → FixedTape.I := splitI ibox423 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox425 : Fin 4 → FixedTape.I := splitI ibox423 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox426 : Fin 4 → FixedTape.I := splitI ibox422 1 135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 true
private noncomputable def ibox427 : Fin 4 → FixedTape.I := splitI ibox426 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox428 : Fin 4 → FixedTape.I := splitI ibox426 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox429 : Fin 4 → FixedTape.I := splitI ibox417 1 162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 true
private noncomputable def ibox430 : Fin 4 → FixedTape.I := splitI ibox429 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox431 : Fin 4 → FixedTape.I := splitI ibox430 1 189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 false
private noncomputable def ibox432 : Fin 4 → FixedTape.I := splitI ibox430 1 189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 true
private noncomputable def ibox433 : Fin 4 → FixedTape.I := splitI ibox429 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox434 : Fin 4 → FixedTape.I := splitI ibox433 1 189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 false
private noncomputable def ibox435 : Fin 4 → FixedTape.I := splitI ibox434 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox436 : Fin 4 → FixedTape.I := splitI ibox434 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox437 : Fin 4 → FixedTape.I := splitI ibox433 1 189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 true
private noncomputable def ibox438 : Fin 4 → FixedTape.I := splitI ibox437 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox439 : Fin 4 → FixedTape.I := splitI ibox437 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox440 : Fin 4 → FixedTape.I := splitI ibox392 1 216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 true
private noncomputable def ibox441 : Fin 4 → FixedTape.I := splitI ibox440 1 324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 false
private noncomputable def ibox442 : Fin 4 → FixedTape.I := splitI ibox441 1 270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 false
private noncomputable def ibox443 : Fin 4 → FixedTape.I := splitI ibox442 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox444 : Fin 4 → FixedTape.I := splitI ibox443 1 243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 false
private noncomputable def ibox445 : Fin 4 → FixedTape.I := splitI ibox443 1 243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 true
private noncomputable def ibox446 : Fin 4 → FixedTape.I := splitI ibox442 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox447 : Fin 4 → FixedTape.I := splitI ibox446 1 243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 false
private noncomputable def ibox448 : Fin 4 → FixedTape.I := splitI ibox447 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox449 : Fin 4 → FixedTape.I := splitI ibox447 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox450 : Fin 4 → FixedTape.I := splitI ibox446 1 243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 true
private noncomputable def ibox451 : Fin 4 → FixedTape.I := splitI ibox450 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox452 : Fin 4 → FixedTape.I := splitI ibox450 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox453 : Fin 4 → FixedTape.I := splitI ibox441 1 270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 true
private noncomputable def ibox454 : Fin 4 → FixedTape.I := splitI ibox453 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox455 : Fin 4 → FixedTape.I := splitI ibox454 1 297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 false
private noncomputable def ibox456 : Fin 4 → FixedTape.I := splitI ibox454 1 297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 true
private noncomputable def ibox457 : Fin 4 → FixedTape.I := splitI ibox453 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox458 : Fin 4 → FixedTape.I := splitI ibox457 1 297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 false
private noncomputable def ibox459 : Fin 4 → FixedTape.I := splitI ibox458 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox460 : Fin 4 → FixedTape.I := splitI ibox458 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox461 : Fin 4 → FixedTape.I := splitI ibox457 1 297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 true
private noncomputable def ibox462 : Fin 4 → FixedTape.I := splitI ibox461 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox463 : Fin 4 → FixedTape.I := splitI ibox461 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox464 : Fin 4 → FixedTape.I := splitI ibox440 1 324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 true
private noncomputable def ibox465 : Fin 4 → FixedTape.I := splitI ibox464 1 378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 false
private noncomputable def ibox466 : Fin 4 → FixedTape.I := splitI ibox465 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox467 : Fin 4 → FixedTape.I := splitI ibox466 1 351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 false
private noncomputable def ibox468 : Fin 4 → FixedTape.I := splitI ibox466 1 351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 true
private noncomputable def ibox469 : Fin 4 → FixedTape.I := splitI ibox465 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox470 : Fin 4 → FixedTape.I := splitI ibox469 1 351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 false
private noncomputable def ibox471 : Fin 4 → FixedTape.I := splitI ibox470 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox472 : Fin 4 → FixedTape.I := splitI ibox470 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox473 : Fin 4 → FixedTape.I := splitI ibox469 1 351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 true
private noncomputable def ibox474 : Fin 4 → FixedTape.I := splitI ibox473 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox475 : Fin 4 → FixedTape.I := splitI ibox473 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox476 : Fin 4 → FixedTape.I := splitI ibox464 1 378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 true
private noncomputable def ibox477 : Fin 4 → FixedTape.I := splitI ibox476 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox478 : Fin 4 → FixedTape.I := splitI ibox477 1 405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 false
private noncomputable def ibox479 : Fin 4 → FixedTape.I := splitI ibox477 1 405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 true
private noncomputable def ibox480 : Fin 4 → FixedTape.I := splitI ibox476 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox481 : Fin 4 → FixedTape.I := splitI ibox480 1 405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 false
private noncomputable def ibox482 : Fin 4 → FixedTape.I := splitI ibox481 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox483 : Fin 4 → FixedTape.I := splitI ibox481 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox484 : Fin 4 → FixedTape.I := splitI ibox480 1 405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 true
private noncomputable def ibox485 : Fin 4 → FixedTape.I := splitI ibox484 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox486 : Fin 4 → FixedTape.I := splitI ibox484 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox487 : Fin 4 → FixedTape.I := splitI ibox263 1 432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 true
private noncomputable def ibox488 : Fin 4 → FixedTape.I := splitI ibox487 1 649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 false
private noncomputable def ibox489 : Fin 4 → FixedTape.I := splitI ibox488 1 540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 false
private noncomputable def ibox490 : Fin 4 → FixedTape.I := splitI ibox489 1 486767162279429328739213547920690205360950627425221026413614394979123200000000000000000000000 false
private noncomputable def ibox491 : Fin 4 → FixedTape.I := splitI ibox490 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox492 : Fin 4 → FixedTape.I := splitI ibox491 1 459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 false
private noncomputable def ibox493 : Fin 4 → FixedTape.I := splitI ibox492 0 831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 false
private noncomputable def ibox494 : Fin 4 → FixedTape.I := splitI ibox492 0 831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 true
private noncomputable def ibox495 : Fin 4 → FixedTape.I := splitI ibox491 1 459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 true
private noncomputable def ibox496 : Fin 4 → FixedTape.I := splitI ibox495 0 831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 false
private noncomputable def ibox497 : Fin 4 → FixedTape.I := splitI ibox495 0 831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 true
private noncomputable def ibox498 : Fin 4 → FixedTape.I := splitI ibox490 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox499 : Fin 4 → FixedTape.I := splitI ibox498 1 459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 false
private noncomputable def ibox500 : Fin 4 → FixedTape.I := splitI ibox499 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox501 : Fin 4 → FixedTape.I := splitI ibox499 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox502 : Fin 4 → FixedTape.I := splitI ibox498 1 459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 true
private noncomputable def ibox503 : Fin 4 → FixedTape.I := splitI ibox502 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox504 : Fin 4 → FixedTape.I := splitI ibox502 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox505 : Fin 4 → FixedTape.I := splitI ibox489 1 486767162279429328739213547920690205360950627425221026413614394979123200000000000000000000000 true
private noncomputable def ibox506 : Fin 4 → FixedTape.I := splitI ibox505 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox507 : Fin 4 → FixedTape.I := splitI ibox506 1 513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 false
private noncomputable def ibox508 : Fin 4 → FixedTape.I := splitI ibox507 0 831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 false
private noncomputable def ibox509 : Fin 4 → FixedTape.I := splitI ibox507 0 831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 true
private noncomputable def ibox510 : Fin 4 → FixedTape.I := splitI ibox506 1 513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 true
private noncomputable def ibox511 : Fin 4 → FixedTape.I := splitI ibox510 0 831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 false
private noncomputable def ibox512 : Fin 4 → FixedTape.I := splitI ibox510 0 831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 true
private noncomputable def ibox513 : Fin 4 → FixedTape.I := splitI ibox505 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox514 : Fin 4 → FixedTape.I := splitI ibox513 1 513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 false
private noncomputable def ibox515 : Fin 4 → FixedTape.I := splitI ibox514 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox516 : Fin 4 → FixedTape.I := splitI ibox514 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox517 : Fin 4 → FixedTape.I := splitI ibox513 1 513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 true
private noncomputable def ibox518 : Fin 4 → FixedTape.I := splitI ibox517 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox519 : Fin 4 → FixedTape.I := splitI ibox517 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox520 : Fin 4 → FixedTape.I := splitI ibox488 1 540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 true
private noncomputable def ibox521 : Fin 4 → FixedTape.I := splitI ibox520 1 594937642785969179570149891903065806552272989075270143394417593863372800000000000000000000000 false
private noncomputable def ibox522 : Fin 4 → FixedTape.I := splitI ibox521 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox523 : Fin 4 → FixedTape.I := splitI ibox522 1 567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 false
private noncomputable def ibox524 : Fin 4 → FixedTape.I := splitI ibox523 0 831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 false
private noncomputable def ibox525 : Fin 4 → FixedTape.I := splitI ibox523 0 831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 true
private noncomputable def ibox526 : Fin 4 → FixedTape.I := splitI ibox522 1 567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 true
private noncomputable def ibox527 : Fin 4 → FixedTape.I := splitI ibox521 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox528 : Fin 4 → FixedTape.I := splitI ibox527 1 567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 false
private noncomputable def ibox529 : Fin 4 → FixedTape.I := splitI ibox528 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox530 : Fin 4 → FixedTape.I := splitI ibox528 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox531 : Fin 4 → FixedTape.I := splitI ibox527 1 567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 true
private noncomputable def ibox532 : Fin 4 → FixedTape.I := splitI ibox531 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox533 : Fin 4 → FixedTape.I := splitI ibox531 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox534 : Fin 4 → FixedTape.I := splitI ibox520 1 594937642785969179570149891903065806552272989075270143394417593863372800000000000000000000000 true
private noncomputable def ibox535 : Fin 4 → FixedTape.I := splitI ibox534 1 621980262912604142277883977898659706850103579487782422639618393584435200000000000000000000000 false
private noncomputable def ibox536 : Fin 4 → FixedTape.I := splitI ibox535 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox537 : Fin 4 → FixedTape.I := splitI ibox535 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox538 : Fin 4 → FixedTape.I := splitI ibox537 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox539 : Fin 4 → FixedTape.I := splitI ibox537 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox540 : Fin 4 → FixedTape.I := splitI ibox534 1 621980262912604142277883977898659706850103579487782422639618393584435200000000000000000000000 true
private noncomputable def ibox541 : Fin 4 → FixedTape.I := splitI ibox540 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox542 : Fin 4 → FixedTape.I := splitI ibox540 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox543 : Fin 4 → FixedTape.I := splitI ibox542 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 false
private noncomputable def ibox544 : Fin 4 → FixedTape.I := splitI ibox542 0 836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 true
private noncomputable def ibox545 : Fin 4 → FixedTape.I := splitI ibox487 1 649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 true
private noncomputable def ibox546 : Fin 4 → FixedTape.I := splitI ibox545 1 757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 false
private noncomputable def ibox547 : Fin 4 → FixedTape.I := splitI ibox546 1 703108123292509030401086235885441407743595350725319260375220792747622400000000000000000000000 false
private noncomputable def ibox548 : Fin 4 → FixedTape.I := splitI ibox547 1 676065503165874067693352149889847507445764760312806981130019993026560000000000000000000000000 false
private noncomputable def ibox549 : Fin 4 → FixedTape.I := splitI ibox548 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox550 : Fin 4 → FixedTape.I := splitI ibox548 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox551 : Fin 4 → FixedTape.I := splitI ibox550 1 662544193102556586339485106892050557296849465106550841507419593166028800000000000000000000000 false
private noncomputable def ibox552 : Fin 4 → FixedTape.I := splitI ibox550 1 662544193102556586339485106892050557296849465106550841507419593166028800000000000000000000000 true
private noncomputable def ibox553 : Fin 4 → FixedTape.I := splitI ibox547 1 676065503165874067693352149889847507445764760312806981130019993026560000000000000000000000000 true
private noncomputable def ibox554 : Fin 4 → FixedTape.I := splitI ibox553 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox555 : Fin 4 → FixedTape.I := splitI ibox553 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox556 : Fin 4 → FixedTape.I := splitI ibox555 1 689586813229191549047219192887644457594680055519063120752620392887091200000000000000000000000 false
private noncomputable def ibox557 : Fin 4 → FixedTape.I := splitI ibox555 1 689586813229191549047219192887644457594680055519063120752620392887091200000000000000000000000 true
private noncomputable def ibox558 : Fin 4 → FixedTape.I := splitI ibox546 1 703108123292509030401086235885441407743595350725319260375220792747622400000000000000000000000 true
private noncomputable def ibox559 : Fin 4 → FixedTape.I := splitI ibox558 1 730150743419143993108820321881035308041425941137831539620421592468684800000000000000000000000 false
private noncomputable def ibox560 : Fin 4 → FixedTape.I := splitI ibox559 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox561 : Fin 4 → FixedTape.I := splitI ibox559 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox562 : Fin 4 → FixedTape.I := splitI ibox561 1 716629433355826511754953278883238357892510645931575399997821192608153600000000000000000000000 false
private noncomputable def ibox563 : Fin 4 → FixedTape.I := splitI ibox561 1 716629433355826511754953278883238357892510645931575399997821192608153600000000000000000000000 true
private noncomputable def ibox564 : Fin 4 → FixedTape.I := splitI ibox558 1 730150743419143993108820321881035308041425941137831539620421592468684800000000000000000000000 true
private noncomputable def ibox565 : Fin 4 → FixedTape.I := splitI ibox564 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 false
private noncomputable def ibox566 : Fin 4 → FixedTape.I := splitI ibox564 0 833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 true
private noncomputable def ibox567 : Fin 4 → FixedTape.I := splitI ibox545 1 757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 true
private noncomputable def ibox568 : Fin 4 → FixedTape.I := splitI ibox567 1 811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 false
private noncomputable def ibox569 : Fin 4 → FixedTape.I := splitI ibox568 1 784235983672413918524288493872223108637087121962856098110823191910809600000000000000000000000 false
private noncomputable def ibox570 : Fin 4 → FixedTape.I := splitI ibox569 1 770714673609096437170421450874426158488171826756599958488222792050278400000000000000000000000 false
private noncomputable def ibox571 : Fin 4 → FixedTape.I := splitI ibox569 1 770714673609096437170421450874426158488171826756599958488222792050278400000000000000000000000 true
private noncomputable def ibox572 : Fin 4 → FixedTape.I := splitI ibox568 1 784235983672413918524288493872223108637087121962856098110823191910809600000000000000000000000 true
private noncomputable def ibox573 : Fin 4 → FixedTape.I := splitI ibox572 1 797757293735731399878155536870020058786002417169112237733423591771340800000000000000000000000 false
private noncomputable def ibox574 : Fin 4 → FixedTape.I := splitI ibox572 1 797757293735731399878155536870020058786002417169112237733423591771340800000000000000000000000 true
private noncomputable def ibox575 : Fin 4 → FixedTape.I := splitI ibox567 1 811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 true
private noncomputable def ibox576 : Fin 4 → FixedTape.I := splitI ibox575 1 838321223925683843939756665863410909232748302787880656601224791352934400000000000000000000000 false
private noncomputable def ibox577 : Fin 4 → FixedTape.I := splitI ibox576 1 824799913862366362585889622865613959083833007581624516978624391492403200000000000000000000000 false
private noncomputable def ibox578 : Fin 4 → FixedTape.I := splitI ibox576 1 824799913862366362585889622865613959083833007581624516978624391492403200000000000000000000000 true
private noncomputable def ibox579 : Fin 4 → FixedTape.I := splitI ibox575 1 838321223925683843939756665863410909232748302787880656601224791352934400000000000000000000000 true
private noncomputable def ibox580 : Fin 4 → FixedTape.I := splitI ibox579 1 851842533989001325293623708861207859381663597994136796223825191213465600000000000000000000000 false
private noncomputable def ibox581 : Fin 4 → FixedTape.I := splitI ibox579 1 851842533989001325293623708861207859381663597994136796223825191213465600000000000000000000000 true
private noncomputable def tree581 : TapeTree := .centered (candidateRows ibox581) (candidateRows (FixedTape.midBox ibox581))
attribute [irreducible] tree581
private theorem sign_581 : 2*denominator*(computed denominator (FixedTape.midBox ibox581)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox581).gradient k).lo.natAbs ((computed denominator ibox581).gradient k).hi.natAbs : Int)*((ibox581 k).hi-(ibox581 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox581
    (computed denominator ibox581) (computed denominator (FixedTape.midBox ibox581))
    (by decide +kernel)
private theorem midpoint_even_581 : ∀ k, 2 ∣ (ibox581 k).lo+(ibox581 k).hi := by decide +kernel
private theorem accepted_581 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox581) tree581 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox581 midpoint_even_581
  simp only [tree581,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox581,candidate_valid h (FixedTape.midBox ibox581),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox581 101 (FixedTape.rowsAux denominator ibox581 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox581) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_581
private noncomputable def tree580 : TapeTree := .centered (candidateRows ibox580) (candidateRows (FixedTape.midBox ibox580))
attribute [irreducible] tree580
private theorem sign_580 : 2*denominator*(computed denominator (FixedTape.midBox ibox580)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox580).gradient k).lo.natAbs ((computed denominator ibox580).gradient k).hi.natAbs : Int)*((ibox580 k).hi-(ibox580 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox580
    (computed denominator ibox580) (computed denominator (FixedTape.midBox ibox580))
    (by decide +kernel)
private theorem midpoint_even_580 : ∀ k, 2 ∣ (ibox580 k).lo+(ibox580 k).hi := by decide +kernel
private theorem accepted_580 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox580) tree580 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox580 midpoint_even_580
  simp only [tree580,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox580,candidate_valid h (FixedTape.midBox ibox580),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox580 101 (FixedTape.rowsAux denominator ibox580 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox580) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_580
private noncomputable def tree579 : TapeTree := .split 1 (((851842533989001325293623708861207859381663597994136796223825191213465600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree580 tree581
attribute [irreducible] tree579
private theorem accepted_579 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox579) tree579 = true := by
  simp only [tree579,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox579 1 (851842533989001325293623708861207859381663597994136796223825191213465600000000000000000000000 : Int) false,decode_split denominator ibox579 1 (851842533989001325293623708861207859381663597994136796223825191213465600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_580 h,accepted_581 h⟩
private noncomputable def tree578 : TapeTree := .centered (candidateRows ibox578) (candidateRows (FixedTape.midBox ibox578))
attribute [irreducible] tree578
private theorem sign_578 : 2*denominator*(computed denominator (FixedTape.midBox ibox578)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox578).gradient k).lo.natAbs ((computed denominator ibox578).gradient k).hi.natAbs : Int)*((ibox578 k).hi-(ibox578 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox578
    (computed denominator ibox578) (computed denominator (FixedTape.midBox ibox578))
    (by decide +kernel)
private theorem midpoint_even_578 : ∀ k, 2 ∣ (ibox578 k).lo+(ibox578 k).hi := by decide +kernel
private theorem accepted_578 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox578) tree578 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox578 midpoint_even_578
  simp only [tree578,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox578,candidate_valid h (FixedTape.midBox ibox578),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox578 101 (FixedTape.rowsAux denominator ibox578 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox578) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_578
private noncomputable def tree577 : TapeTree := .centered (candidateRows ibox577) (candidateRows (FixedTape.midBox ibox577))
attribute [irreducible] tree577
private theorem sign_577 : 2*denominator*(computed denominator (FixedTape.midBox ibox577)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox577).gradient k).lo.natAbs ((computed denominator ibox577).gradient k).hi.natAbs : Int)*((ibox577 k).hi-(ibox577 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox577
    (computed denominator ibox577) (computed denominator (FixedTape.midBox ibox577))
    (by decide +kernel)
private theorem midpoint_even_577 : ∀ k, 2 ∣ (ibox577 k).lo+(ibox577 k).hi := by decide +kernel
private theorem accepted_577 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox577) tree577 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox577 midpoint_even_577
  simp only [tree577,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox577,candidate_valid h (FixedTape.midBox ibox577),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox577 101 (FixedTape.rowsAux denominator ibox577 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox577) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_577
private noncomputable def tree576 : TapeTree := .split 1 (((824799913862366362585889622865613959083833007581624516978624391492403200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree577 tree578
attribute [irreducible] tree576
private theorem accepted_576 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox576) tree576 = true := by
  simp only [tree576,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox576 1 (824799913862366362585889622865613959083833007581624516978624391492403200000000000000000000000 : Int) false,decode_split denominator ibox576 1 (824799913862366362585889622865613959083833007581624516978624391492403200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_577 h,accepted_578 h⟩
private noncomputable def tree575 : TapeTree := .split 1 (((838321223925683843939756665863410909232748302787880656601224791352934400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree576 tree579
attribute [irreducible] tree575
private theorem accepted_575 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox575) tree575 = true := by
  simp only [tree575,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox575 1 (838321223925683843939756665863410909232748302787880656601224791352934400000000000000000000000 : Int) false,decode_split denominator ibox575 1 (838321223925683843939756665863410909232748302787880656601224791352934400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_576 h,accepted_579 h⟩
private noncomputable def tree574 : TapeTree := .centered (candidateRows ibox574) (candidateRows (FixedTape.midBox ibox574))
attribute [irreducible] tree574
private theorem sign_574 : 2*denominator*(computed denominator (FixedTape.midBox ibox574)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox574).gradient k).lo.natAbs ((computed denominator ibox574).gradient k).hi.natAbs : Int)*((ibox574 k).hi-(ibox574 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox574
    (computed denominator ibox574) (computed denominator (FixedTape.midBox ibox574))
    (by decide +kernel)
private theorem midpoint_even_574 : ∀ k, 2 ∣ (ibox574 k).lo+(ibox574 k).hi := by decide +kernel
private theorem accepted_574 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox574) tree574 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox574 midpoint_even_574
  simp only [tree574,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox574,candidate_valid h (FixedTape.midBox ibox574),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox574 101 (FixedTape.rowsAux denominator ibox574 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox574) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_574
private noncomputable def tree573 : TapeTree := .centered (candidateRows ibox573) (candidateRows (FixedTape.midBox ibox573))
attribute [irreducible] tree573
private theorem sign_573 : 2*denominator*(computed denominator (FixedTape.midBox ibox573)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox573).gradient k).lo.natAbs ((computed denominator ibox573).gradient k).hi.natAbs : Int)*((ibox573 k).hi-(ibox573 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox573
    (computed denominator ibox573) (computed denominator (FixedTape.midBox ibox573))
    (by decide +kernel)
private theorem midpoint_even_573 : ∀ k, 2 ∣ (ibox573 k).lo+(ibox573 k).hi := by decide +kernel
private theorem accepted_573 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox573) tree573 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox573 midpoint_even_573
  simp only [tree573,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox573,candidate_valid h (FixedTape.midBox ibox573),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox573 101 (FixedTape.rowsAux denominator ibox573 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox573) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_573
private noncomputable def tree572 : TapeTree := .split 1 (((797757293735731399878155536870020058786002417169112237733423591771340800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree573 tree574
attribute [irreducible] tree572
private theorem accepted_572 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox572) tree572 = true := by
  simp only [tree572,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox572 1 (797757293735731399878155536870020058786002417169112237733423591771340800000000000000000000000 : Int) false,decode_split denominator ibox572 1 (797757293735731399878155536870020058786002417169112237733423591771340800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_573 h,accepted_574 h⟩
private noncomputable def tree571 : TapeTree := .centered (candidateRows ibox571) (candidateRows (FixedTape.midBox ibox571))
attribute [irreducible] tree571
private theorem sign_571 : 2*denominator*(computed denominator (FixedTape.midBox ibox571)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox571).gradient k).lo.natAbs ((computed denominator ibox571).gradient k).hi.natAbs : Int)*((ibox571 k).hi-(ibox571 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox571
    (computed denominator ibox571) (computed denominator (FixedTape.midBox ibox571))
    (by decide +kernel)
private theorem midpoint_even_571 : ∀ k, 2 ∣ (ibox571 k).lo+(ibox571 k).hi := by decide +kernel
private theorem accepted_571 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox571) tree571 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox571 midpoint_even_571
  simp only [tree571,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox571,candidate_valid h (FixedTape.midBox ibox571),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox571 101 (FixedTape.rowsAux denominator ibox571 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox571) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_571
private noncomputable def tree570 : TapeTree := .centered (candidateRows ibox570) (candidateRows (FixedTape.midBox ibox570))
attribute [irreducible] tree570
private theorem sign_570 : 2*denominator*(computed denominator (FixedTape.midBox ibox570)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox570).gradient k).lo.natAbs ((computed denominator ibox570).gradient k).hi.natAbs : Int)*((ibox570 k).hi-(ibox570 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox570
    (computed denominator ibox570) (computed denominator (FixedTape.midBox ibox570))
    (by decide +kernel)
private theorem midpoint_even_570 : ∀ k, 2 ∣ (ibox570 k).lo+(ibox570 k).hi := by decide +kernel
private theorem accepted_570 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox570) tree570 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox570 midpoint_even_570
  simp only [tree570,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox570,candidate_valid h (FixedTape.midBox ibox570),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox570 101 (FixedTape.rowsAux denominator ibox570 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox570) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_570
private noncomputable def tree569 : TapeTree := .split 1 (((770714673609096437170421450874426158488171826756599958488222792050278400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree570 tree571
attribute [irreducible] tree569
private theorem accepted_569 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox569) tree569 = true := by
  simp only [tree569,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox569 1 (770714673609096437170421450874426158488171826756599958488222792050278400000000000000000000000 : Int) false,decode_split denominator ibox569 1 (770714673609096437170421450874426158488171826756599958488222792050278400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_570 h,accepted_571 h⟩
private noncomputable def tree568 : TapeTree := .split 1 (((784235983672413918524288493872223108637087121962856098110823191910809600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree569 tree572
attribute [irreducible] tree568
private theorem accepted_568 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox568) tree568 = true := by
  simp only [tree568,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox568 1 (784235983672413918524288493872223108637087121962856098110823191910809600000000000000000000000 : Int) false,decode_split denominator ibox568 1 (784235983672413918524288493872223108637087121962856098110823191910809600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_569 h,accepted_572 h⟩
private noncomputable def tree567 : TapeTree := .split 1 (((811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree568 tree575
attribute [irreducible] tree567
private theorem accepted_567 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox567) tree567 = true := by
  simp only [tree567,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox567 1 (811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 : Int) false,decode_split denominator ibox567 1 (811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_568 h,accepted_575 h⟩
private noncomputable def tree566 : TapeTree := .centered (candidateRows ibox566) (candidateRows (FixedTape.midBox ibox566))
attribute [irreducible] tree566
private theorem sign_566 : 2*denominator*(computed denominator (FixedTape.midBox ibox566)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox566).gradient k).lo.natAbs ((computed denominator ibox566).gradient k).hi.natAbs : Int)*((ibox566 k).hi-(ibox566 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox566
    (computed denominator ibox566) (computed denominator (FixedTape.midBox ibox566))
    (by decide +kernel)
private theorem midpoint_even_566 : ∀ k, 2 ∣ (ibox566 k).lo+(ibox566 k).hi := by decide +kernel
private theorem accepted_566 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox566) tree566 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox566 midpoint_even_566
  simp only [tree566,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox566,candidate_valid h (FixedTape.midBox ibox566),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox566 101 (FixedTape.rowsAux denominator ibox566 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox566) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_566
private noncomputable def tree565 : TapeTree := .centered (candidateRows ibox565) (candidateRows (FixedTape.midBox ibox565))
attribute [irreducible] tree565
private theorem sign_565 : 2*denominator*(computed denominator (FixedTape.midBox ibox565)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox565).gradient k).lo.natAbs ((computed denominator ibox565).gradient k).hi.natAbs : Int)*((ibox565 k).hi-(ibox565 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox565
    (computed denominator ibox565) (computed denominator (FixedTape.midBox ibox565))
    (by decide +kernel)
private theorem midpoint_even_565 : ∀ k, 2 ∣ (ibox565 k).lo+(ibox565 k).hi := by decide +kernel
private theorem accepted_565 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox565) tree565 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox565 midpoint_even_565
  simp only [tree565,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox565,candidate_valid h (FixedTape.midBox ibox565),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox565 101 (FixedTape.rowsAux denominator ibox565 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox565) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_565
private noncomputable def tree564 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree565 tree566
attribute [irreducible] tree564
private theorem accepted_564 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox564) tree564 = true := by
  simp only [tree564,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox564 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox564 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_565 h,accepted_566 h⟩
private noncomputable def tree563 : TapeTree := .centered (candidateRows ibox563) (candidateRows (FixedTape.midBox ibox563))
attribute [irreducible] tree563
private theorem sign_563 : 2*denominator*(computed denominator (FixedTape.midBox ibox563)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox563).gradient k).lo.natAbs ((computed denominator ibox563).gradient k).hi.natAbs : Int)*((ibox563 k).hi-(ibox563 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox563
    (computed denominator ibox563) (computed denominator (FixedTape.midBox ibox563))
    (by decide +kernel)
private theorem midpoint_even_563 : ∀ k, 2 ∣ (ibox563 k).lo+(ibox563 k).hi := by decide +kernel
private theorem accepted_563 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox563) tree563 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox563 midpoint_even_563
  simp only [tree563,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox563,candidate_valid h (FixedTape.midBox ibox563),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox563 101 (FixedTape.rowsAux denominator ibox563 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox563) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_563
private noncomputable def tree562 : TapeTree := .centered (candidateRows ibox562) (candidateRows (FixedTape.midBox ibox562))
attribute [irreducible] tree562
private theorem sign_562 : 2*denominator*(computed denominator (FixedTape.midBox ibox562)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox562).gradient k).lo.natAbs ((computed denominator ibox562).gradient k).hi.natAbs : Int)*((ibox562 k).hi-(ibox562 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox562
    (computed denominator ibox562) (computed denominator (FixedTape.midBox ibox562))
    (by decide +kernel)
private theorem midpoint_even_562 : ∀ k, 2 ∣ (ibox562 k).lo+(ibox562 k).hi := by decide +kernel
private theorem accepted_562 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox562) tree562 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox562 midpoint_even_562
  simp only [tree562,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox562,candidate_valid h (FixedTape.midBox ibox562),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox562 101 (FixedTape.rowsAux denominator ibox562 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox562) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_562
private noncomputable def tree561 : TapeTree := .split 1 (((716629433355826511754953278883238357892510645931575399997821192608153600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree562 tree563
attribute [irreducible] tree561
private theorem accepted_561 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox561) tree561 = true := by
  simp only [tree561,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox561 1 (716629433355826511754953278883238357892510645931575399997821192608153600000000000000000000000 : Int) false,decode_split denominator ibox561 1 (716629433355826511754953278883238357892510645931575399997821192608153600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_562 h,accepted_563 h⟩
private noncomputable def tree560 : TapeTree := .centered (candidateRows ibox560) (candidateRows (FixedTape.midBox ibox560))
attribute [irreducible] tree560
private theorem sign_560 : 2*denominator*(computed denominator (FixedTape.midBox ibox560)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox560).gradient k).lo.natAbs ((computed denominator ibox560).gradient k).hi.natAbs : Int)*((ibox560 k).hi-(ibox560 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox560
    (computed denominator ibox560) (computed denominator (FixedTape.midBox ibox560))
    (by decide +kernel)
private theorem midpoint_even_560 : ∀ k, 2 ∣ (ibox560 k).lo+(ibox560 k).hi := by decide +kernel
private theorem accepted_560 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox560) tree560 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox560 midpoint_even_560
  simp only [tree560,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox560,candidate_valid h (FixedTape.midBox ibox560),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox560 101 (FixedTape.rowsAux denominator ibox560 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox560) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_560
private noncomputable def tree559 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree560 tree561
attribute [irreducible] tree559
private theorem accepted_559 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox559) tree559 = true := by
  simp only [tree559,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox559 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox559 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_560 h,accepted_561 h⟩
private noncomputable def tree558 : TapeTree := .split 1 (((730150743419143993108820321881035308041425941137831539620421592468684800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree559 tree564
attribute [irreducible] tree558
private theorem accepted_558 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox558) tree558 = true := by
  simp only [tree558,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox558 1 (730150743419143993108820321881035308041425941137831539620421592468684800000000000000000000000 : Int) false,decode_split denominator ibox558 1 (730150743419143993108820321881035308041425941137831539620421592468684800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_559 h,accepted_564 h⟩
private noncomputable def tree557 : TapeTree := .centered (candidateRows ibox557) (candidateRows (FixedTape.midBox ibox557))
attribute [irreducible] tree557
private theorem sign_557 : 2*denominator*(computed denominator (FixedTape.midBox ibox557)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox557).gradient k).lo.natAbs ((computed denominator ibox557).gradient k).hi.natAbs : Int)*((ibox557 k).hi-(ibox557 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox557
    (computed denominator ibox557) (computed denominator (FixedTape.midBox ibox557))
    (by decide +kernel)
private theorem midpoint_even_557 : ∀ k, 2 ∣ (ibox557 k).lo+(ibox557 k).hi := by decide +kernel
private theorem accepted_557 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox557) tree557 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox557 midpoint_even_557
  simp only [tree557,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox557,candidate_valid h (FixedTape.midBox ibox557),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox557 101 (FixedTape.rowsAux denominator ibox557 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox557) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_557
private noncomputable def tree556 : TapeTree := .centered (candidateRows ibox556) (candidateRows (FixedTape.midBox ibox556))
attribute [irreducible] tree556
private theorem sign_556 : 2*denominator*(computed denominator (FixedTape.midBox ibox556)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox556).gradient k).lo.natAbs ((computed denominator ibox556).gradient k).hi.natAbs : Int)*((ibox556 k).hi-(ibox556 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox556
    (computed denominator ibox556) (computed denominator (FixedTape.midBox ibox556))
    (by decide +kernel)
private theorem midpoint_even_556 : ∀ k, 2 ∣ (ibox556 k).lo+(ibox556 k).hi := by decide +kernel
private theorem accepted_556 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox556) tree556 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox556 midpoint_even_556
  simp only [tree556,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox556,candidate_valid h (FixedTape.midBox ibox556),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox556 101 (FixedTape.rowsAux denominator ibox556 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox556) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_556
private noncomputable def tree555 : TapeTree := .split 1 (((689586813229191549047219192887644457594680055519063120752620392887091200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree556 tree557
attribute [irreducible] tree555
private theorem accepted_555 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox555) tree555 = true := by
  simp only [tree555,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox555 1 (689586813229191549047219192887644457594680055519063120752620392887091200000000000000000000000 : Int) false,decode_split denominator ibox555 1 (689586813229191549047219192887644457594680055519063120752620392887091200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_556 h,accepted_557 h⟩
private noncomputable def tree554 : TapeTree := .centered (candidateRows ibox554) (candidateRows (FixedTape.midBox ibox554))
attribute [irreducible] tree554
private theorem sign_554 : 2*denominator*(computed denominator (FixedTape.midBox ibox554)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox554).gradient k).lo.natAbs ((computed denominator ibox554).gradient k).hi.natAbs : Int)*((ibox554 k).hi-(ibox554 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox554
    (computed denominator ibox554) (computed denominator (FixedTape.midBox ibox554))
    (by decide +kernel)
private theorem midpoint_even_554 : ∀ k, 2 ∣ (ibox554 k).lo+(ibox554 k).hi := by decide +kernel
private theorem accepted_554 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox554) tree554 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox554 midpoint_even_554
  simp only [tree554,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox554,candidate_valid h (FixedTape.midBox ibox554),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox554 101 (FixedTape.rowsAux denominator ibox554 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox554) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_554
private noncomputable def tree553 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree554 tree555
attribute [irreducible] tree553
private theorem accepted_553 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox553) tree553 = true := by
  simp only [tree553,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox553 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox553 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_554 h,accepted_555 h⟩
private noncomputable def tree552 : TapeTree := .centered (candidateRows ibox552) (candidateRows (FixedTape.midBox ibox552))
attribute [irreducible] tree552
private theorem sign_552 : 2*denominator*(computed denominator (FixedTape.midBox ibox552)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox552).gradient k).lo.natAbs ((computed denominator ibox552).gradient k).hi.natAbs : Int)*((ibox552 k).hi-(ibox552 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox552
    (computed denominator ibox552) (computed denominator (FixedTape.midBox ibox552))
    (by decide +kernel)
private theorem midpoint_even_552 : ∀ k, 2 ∣ (ibox552 k).lo+(ibox552 k).hi := by decide +kernel
private theorem accepted_552 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox552) tree552 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox552 midpoint_even_552
  simp only [tree552,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox552,candidate_valid h (FixedTape.midBox ibox552),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox552 101 (FixedTape.rowsAux denominator ibox552 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox552) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_552
private noncomputable def tree551 : TapeTree := .centered (candidateRows ibox551) (candidateRows (FixedTape.midBox ibox551))
attribute [irreducible] tree551
private theorem sign_551 : 2*denominator*(computed denominator (FixedTape.midBox ibox551)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox551).gradient k).lo.natAbs ((computed denominator ibox551).gradient k).hi.natAbs : Int)*((ibox551 k).hi-(ibox551 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox551
    (computed denominator ibox551) (computed denominator (FixedTape.midBox ibox551))
    (by decide +kernel)
private theorem midpoint_even_551 : ∀ k, 2 ∣ (ibox551 k).lo+(ibox551 k).hi := by decide +kernel
private theorem accepted_551 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox551) tree551 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox551 midpoint_even_551
  simp only [tree551,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox551,candidate_valid h (FixedTape.midBox ibox551),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox551 101 (FixedTape.rowsAux denominator ibox551 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox551) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_551
private noncomputable def tree550 : TapeTree := .split 1 (((662544193102556586339485106892050557296849465106550841507419593166028800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree551 tree552
attribute [irreducible] tree550
private theorem accepted_550 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox550) tree550 = true := by
  simp only [tree550,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox550 1 (662544193102556586339485106892050557296849465106550841507419593166028800000000000000000000000 : Int) false,decode_split denominator ibox550 1 (662544193102556586339485106892050557296849465106550841507419593166028800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_551 h,accepted_552 h⟩
private noncomputable def tree549 : TapeTree := .centered (candidateRows ibox549) (candidateRows (FixedTape.midBox ibox549))
attribute [irreducible] tree549
private theorem sign_549 : 2*denominator*(computed denominator (FixedTape.midBox ibox549)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox549).gradient k).lo.natAbs ((computed denominator ibox549).gradient k).hi.natAbs : Int)*((ibox549 k).hi-(ibox549 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox549
    (computed denominator ibox549) (computed denominator (FixedTape.midBox ibox549))
    (by decide +kernel)
private theorem midpoint_even_549 : ∀ k, 2 ∣ (ibox549 k).lo+(ibox549 k).hi := by decide +kernel
private theorem accepted_549 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox549) tree549 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox549 midpoint_even_549
  simp only [tree549,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox549,candidate_valid h (FixedTape.midBox ibox549),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox549 101 (FixedTape.rowsAux denominator ibox549 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox549) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_549
private noncomputable def tree548 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree549 tree550
attribute [irreducible] tree548
private theorem accepted_548 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox548) tree548 = true := by
  simp only [tree548,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox548 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox548 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_549 h,accepted_550 h⟩
private noncomputable def tree547 : TapeTree := .split 1 (((676065503165874067693352149889847507445764760312806981130019993026560000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree548 tree553
attribute [irreducible] tree547
private theorem accepted_547 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox547) tree547 = true := by
  simp only [tree547,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox547 1 (676065503165874067693352149889847507445764760312806981130019993026560000000000000000000000000 : Int) false,decode_split denominator ibox547 1 (676065503165874067693352149889847507445764760312806981130019993026560000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_548 h,accepted_553 h⟩
private noncomputable def tree546 : TapeTree := .split 1 (((703108123292509030401086235885441407743595350725319260375220792747622400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree547 tree558
attribute [irreducible] tree546
private theorem accepted_546 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox546) tree546 = true := by
  simp only [tree546,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox546 1 (703108123292509030401086235885441407743595350725319260375220792747622400000000000000000000000 : Int) false,decode_split denominator ibox546 1 (703108123292509030401086235885441407743595350725319260375220792747622400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_547 h,accepted_558 h⟩
private noncomputable def tree545 : TapeTree := .split 1 (((757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree546 tree567
attribute [irreducible] tree545
private theorem accepted_545 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox545) tree545 = true := by
  simp only [tree545,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox545 1 (757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 : Int) false,decode_split denominator ibox545 1 (757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_546 h,accepted_567 h⟩
private noncomputable def tree544 : TapeTree := .centered (candidateRows ibox544) (candidateRows (FixedTape.midBox ibox544))
attribute [irreducible] tree544
private theorem sign_544 : 2*denominator*(computed denominator (FixedTape.midBox ibox544)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox544).gradient k).lo.natAbs ((computed denominator ibox544).gradient k).hi.natAbs : Int)*((ibox544 k).hi-(ibox544 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox544
    (computed denominator ibox544) (computed denominator (FixedTape.midBox ibox544))
    (by decide +kernel)
private theorem midpoint_even_544 : ∀ k, 2 ∣ (ibox544 k).lo+(ibox544 k).hi := by decide +kernel
private theorem accepted_544 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox544) tree544 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox544 midpoint_even_544
  simp only [tree544,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox544,candidate_valid h (FixedTape.midBox ibox544),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox544 101 (FixedTape.rowsAux denominator ibox544 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox544) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_544
private noncomputable def tree543 : TapeTree := .centered (candidateRows ibox543) (candidateRows (FixedTape.midBox ibox543))
attribute [irreducible] tree543
private theorem sign_543 : 2*denominator*(computed denominator (FixedTape.midBox ibox543)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox543).gradient k).lo.natAbs ((computed denominator ibox543).gradient k).hi.natAbs : Int)*((ibox543 k).hi-(ibox543 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox543
    (computed denominator ibox543) (computed denominator (FixedTape.midBox ibox543))
    (by decide +kernel)
private theorem midpoint_even_543 : ∀ k, 2 ∣ (ibox543 k).lo+(ibox543 k).hi := by decide +kernel
private theorem accepted_543 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox543) tree543 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox543 midpoint_even_543
  simp only [tree543,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox543,candidate_valid h (FixedTape.midBox ibox543),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox543 101 (FixedTape.rowsAux denominator ibox543 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox543) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_543
private noncomputable def tree542 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree543 tree544
attribute [irreducible] tree542
private theorem accepted_542 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox542) tree542 = true := by
  simp only [tree542,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox542 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox542 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_543 h,accepted_544 h⟩
private noncomputable def tree541 : TapeTree := .centered (candidateRows ibox541) (candidateRows (FixedTape.midBox ibox541))
attribute [irreducible] tree541
private theorem sign_541 : 2*denominator*(computed denominator (FixedTape.midBox ibox541)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox541).gradient k).lo.natAbs ((computed denominator ibox541).gradient k).hi.natAbs : Int)*((ibox541 k).hi-(ibox541 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox541
    (computed denominator ibox541) (computed denominator (FixedTape.midBox ibox541))
    (by decide +kernel)
private theorem midpoint_even_541 : ∀ k, 2 ∣ (ibox541 k).lo+(ibox541 k).hi := by decide +kernel
private theorem accepted_541 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox541) tree541 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox541 midpoint_even_541
  simp only [tree541,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox541,candidate_valid h (FixedTape.midBox ibox541),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox541 101 (FixedTape.rowsAux denominator ibox541 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox541) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_541
private noncomputable def tree540 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree541 tree542
attribute [irreducible] tree540
private theorem accepted_540 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox540) tree540 = true := by
  simp only [tree540,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox540 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox540 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_541 h,accepted_542 h⟩
private noncomputable def tree539 : TapeTree := .centered (candidateRows ibox539) (candidateRows (FixedTape.midBox ibox539))
attribute [irreducible] tree539
private theorem sign_539 : 2*denominator*(computed denominator (FixedTape.midBox ibox539)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox539).gradient k).lo.natAbs ((computed denominator ibox539).gradient k).hi.natAbs : Int)*((ibox539 k).hi-(ibox539 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox539
    (computed denominator ibox539) (computed denominator (FixedTape.midBox ibox539))
    (by decide +kernel)
private theorem midpoint_even_539 : ∀ k, 2 ∣ (ibox539 k).lo+(ibox539 k).hi := by decide +kernel
private theorem accepted_539 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox539) tree539 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox539 midpoint_even_539
  simp only [tree539,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox539,candidate_valid h (FixedTape.midBox ibox539),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox539 101 (FixedTape.rowsAux denominator ibox539 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox539) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_539
private noncomputable def tree538 : TapeTree := .centered (candidateRows ibox538) (candidateRows (FixedTape.midBox ibox538))
attribute [irreducible] tree538
private theorem sign_538 : 2*denominator*(computed denominator (FixedTape.midBox ibox538)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox538).gradient k).lo.natAbs ((computed denominator ibox538).gradient k).hi.natAbs : Int)*((ibox538 k).hi-(ibox538 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox538
    (computed denominator ibox538) (computed denominator (FixedTape.midBox ibox538))
    (by decide +kernel)
private theorem midpoint_even_538 : ∀ k, 2 ∣ (ibox538 k).lo+(ibox538 k).hi := by decide +kernel
private theorem accepted_538 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox538) tree538 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox538 midpoint_even_538
  simp only [tree538,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox538,candidate_valid h (FixedTape.midBox ibox538),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox538 101 (FixedTape.rowsAux denominator ibox538 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox538) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_538
private noncomputable def tree537 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree538 tree539
attribute [irreducible] tree537
private theorem accepted_537 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox537) tree537 = true := by
  simp only [tree537,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox537 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox537 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_538 h,accepted_539 h⟩
private noncomputable def tree536 : TapeTree := .centered (candidateRows ibox536) (candidateRows (FixedTape.midBox ibox536))
attribute [irreducible] tree536
private theorem sign_536 : 2*denominator*(computed denominator (FixedTape.midBox ibox536)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox536).gradient k).lo.natAbs ((computed denominator ibox536).gradient k).hi.natAbs : Int)*((ibox536 k).hi-(ibox536 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox536
    (computed denominator ibox536) (computed denominator (FixedTape.midBox ibox536))
    (by decide +kernel)
private theorem midpoint_even_536 : ∀ k, 2 ∣ (ibox536 k).lo+(ibox536 k).hi := by decide +kernel
private theorem accepted_536 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox536) tree536 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox536 midpoint_even_536
  simp only [tree536,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox536,candidate_valid h (FixedTape.midBox ibox536),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox536 101 (FixedTape.rowsAux denominator ibox536 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox536) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_536
private noncomputable def tree535 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree536 tree537
attribute [irreducible] tree535
private theorem accepted_535 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox535) tree535 = true := by
  simp only [tree535,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox535 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox535 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_536 h,accepted_537 h⟩
private noncomputable def tree534 : TapeTree := .split 1 (((621980262912604142277883977898659706850103579487782422639618393584435200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree535 tree540
attribute [irreducible] tree534
private theorem accepted_534 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox534) tree534 = true := by
  simp only [tree534,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox534 1 (621980262912604142277883977898659706850103579487782422639618393584435200000000000000000000000 : Int) false,decode_split denominator ibox534 1 (621980262912604142277883977898659706850103579487782422639618393584435200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_535 h,accepted_540 h⟩
private noncomputable def tree533 : TapeTree := .centered (candidateRows ibox533) (candidateRows (FixedTape.midBox ibox533))
attribute [irreducible] tree533
private theorem sign_533 : 2*denominator*(computed denominator (FixedTape.midBox ibox533)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox533).gradient k).lo.natAbs ((computed denominator ibox533).gradient k).hi.natAbs : Int)*((ibox533 k).hi-(ibox533 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox533
    (computed denominator ibox533) (computed denominator (FixedTape.midBox ibox533))
    (by decide +kernel)
private theorem midpoint_even_533 : ∀ k, 2 ∣ (ibox533 k).lo+(ibox533 k).hi := by decide +kernel
private theorem accepted_533 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox533) tree533 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox533 midpoint_even_533
  simp only [tree533,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox533,candidate_valid h (FixedTape.midBox ibox533),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox533 101 (FixedTape.rowsAux denominator ibox533 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox533) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_533
private noncomputable def tree532 : TapeTree := .centered (candidateRows ibox532) (candidateRows (FixedTape.midBox ibox532))
attribute [irreducible] tree532
private theorem sign_532 : 2*denominator*(computed denominator (FixedTape.midBox ibox532)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox532).gradient k).lo.natAbs ((computed denominator ibox532).gradient k).hi.natAbs : Int)*((ibox532 k).hi-(ibox532 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox532
    (computed denominator ibox532) (computed denominator (FixedTape.midBox ibox532))
    (by decide +kernel)
private theorem midpoint_even_532 : ∀ k, 2 ∣ (ibox532 k).lo+(ibox532 k).hi := by decide +kernel
private theorem accepted_532 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox532) tree532 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox532 midpoint_even_532
  simp only [tree532,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox532,candidate_valid h (FixedTape.midBox ibox532),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox532 101 (FixedTape.rowsAux denominator ibox532 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox532) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_532
private noncomputable def tree531 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree532 tree533
attribute [irreducible] tree531
private theorem accepted_531 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox531) tree531 = true := by
  simp only [tree531,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox531 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox531 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_532 h,accepted_533 h⟩
private noncomputable def tree530 : TapeTree := .centered (candidateRows ibox530) (candidateRows (FixedTape.midBox ibox530))
attribute [irreducible] tree530
private theorem sign_530 : 2*denominator*(computed denominator (FixedTape.midBox ibox530)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox530).gradient k).lo.natAbs ((computed denominator ibox530).gradient k).hi.natAbs : Int)*((ibox530 k).hi-(ibox530 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox530
    (computed denominator ibox530) (computed denominator (FixedTape.midBox ibox530))
    (by decide +kernel)
private theorem midpoint_even_530 : ∀ k, 2 ∣ (ibox530 k).lo+(ibox530 k).hi := by decide +kernel
private theorem accepted_530 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox530) tree530 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox530 midpoint_even_530
  simp only [tree530,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox530,candidate_valid h (FixedTape.midBox ibox530),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox530 101 (FixedTape.rowsAux denominator ibox530 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox530) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_530
private noncomputable def tree529 : TapeTree := .centered (candidateRows ibox529) (candidateRows (FixedTape.midBox ibox529))
attribute [irreducible] tree529
private theorem sign_529 : 2*denominator*(computed denominator (FixedTape.midBox ibox529)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox529).gradient k).lo.natAbs ((computed denominator ibox529).gradient k).hi.natAbs : Int)*((ibox529 k).hi-(ibox529 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox529
    (computed denominator ibox529) (computed denominator (FixedTape.midBox ibox529))
    (by decide +kernel)
private theorem midpoint_even_529 : ∀ k, 2 ∣ (ibox529 k).lo+(ibox529 k).hi := by decide +kernel
private theorem accepted_529 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox529) tree529 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox529 midpoint_even_529
  simp only [tree529,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox529,candidate_valid h (FixedTape.midBox ibox529),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox529 101 (FixedTape.rowsAux denominator ibox529 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox529) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_529
private noncomputable def tree528 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree529 tree530
attribute [irreducible] tree528
private theorem accepted_528 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox528) tree528 = true := by
  simp only [tree528,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox528 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox528 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_529 h,accepted_530 h⟩
private noncomputable def tree527 : TapeTree := .split 1 (((567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree528 tree531
attribute [irreducible] tree527
private theorem accepted_527 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox527) tree527 = true := by
  simp only [tree527,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox527 1 (567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 : Int) false,decode_split denominator ibox527 1 (567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_528 h,accepted_531 h⟩
private noncomputable def tree526 : TapeTree := .centered (candidateRows ibox526) (candidateRows (FixedTape.midBox ibox526))
attribute [irreducible] tree526
private theorem sign_526 : 2*denominator*(computed denominator (FixedTape.midBox ibox526)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox526).gradient k).lo.natAbs ((computed denominator ibox526).gradient k).hi.natAbs : Int)*((ibox526 k).hi-(ibox526 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox526
    (computed denominator ibox526) (computed denominator (FixedTape.midBox ibox526))
    (by decide +kernel)
private theorem midpoint_even_526 : ∀ k, 2 ∣ (ibox526 k).lo+(ibox526 k).hi := by decide +kernel
private theorem accepted_526 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox526) tree526 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox526 midpoint_even_526
  simp only [tree526,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox526,candidate_valid h (FixedTape.midBox ibox526),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox526 101 (FixedTape.rowsAux denominator ibox526 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox526) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_526
private noncomputable def tree525 : TapeTree := .centered (candidateRows ibox525) (candidateRows (FixedTape.midBox ibox525))
attribute [irreducible] tree525
private theorem sign_525 : 2*denominator*(computed denominator (FixedTape.midBox ibox525)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox525).gradient k).lo.natAbs ((computed denominator ibox525).gradient k).hi.natAbs : Int)*((ibox525 k).hi-(ibox525 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox525
    (computed denominator ibox525) (computed denominator (FixedTape.midBox ibox525))
    (by decide +kernel)
private theorem midpoint_even_525 : ∀ k, 2 ∣ (ibox525 k).lo+(ibox525 k).hi := by decide +kernel
private theorem accepted_525 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox525) tree525 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox525 midpoint_even_525
  simp only [tree525,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox525,candidate_valid h (FixedTape.midBox ibox525),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox525 101 (FixedTape.rowsAux denominator ibox525 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox525) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_525
private noncomputable def tree524 : TapeTree := .centered (candidateRows ibox524) (candidateRows (FixedTape.midBox ibox524))
attribute [irreducible] tree524
private theorem sign_524 : 2*denominator*(computed denominator (FixedTape.midBox ibox524)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox524).gradient k).lo.natAbs ((computed denominator ibox524).gradient k).hi.natAbs : Int)*((ibox524 k).hi-(ibox524 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox524
    (computed denominator ibox524) (computed denominator (FixedTape.midBox ibox524))
    (by decide +kernel)
private theorem midpoint_even_524 : ∀ k, 2 ∣ (ibox524 k).lo+(ibox524 k).hi := by decide +kernel
private theorem accepted_524 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox524) tree524 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox524 midpoint_even_524
  simp only [tree524,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox524,candidate_valid h (FixedTape.midBox ibox524),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox524 101 (FixedTape.rowsAux denominator ibox524 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox524) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_524
private noncomputable def tree523 : TapeTree := .split 0 (((831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 : Int) : ℚ)/(denominator : ℚ)) tree524 tree525
attribute [irreducible] tree523
private theorem accepted_523 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox523) tree523 = true := by
  simp only [tree523,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox523 0 (831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 : Int) false,decode_split denominator ibox523 0 (831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_524 h,accepted_525 h⟩
private noncomputable def tree522 : TapeTree := .split 1 (((567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree523 tree526
attribute [irreducible] tree522
private theorem accepted_522 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox522) tree522 = true := by
  simp only [tree522,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox522 1 (567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 : Int) false,decode_split denominator ibox522 1 (567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_523 h,accepted_526 h⟩
private noncomputable def tree521 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree522 tree527
attribute [irreducible] tree521
private theorem accepted_521 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox521) tree521 = true := by
  simp only [tree521,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox521 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox521 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_522 h,accepted_527 h⟩
private noncomputable def tree520 : TapeTree := .split 1 (((594937642785969179570149891903065806552272989075270143394417593863372800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree521 tree534
attribute [irreducible] tree520
private theorem accepted_520 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox520) tree520 = true := by
  simp only [tree520,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox520 1 (594937642785969179570149891903065806552272989075270143394417593863372800000000000000000000000 : Int) false,decode_split denominator ibox520 1 (594937642785969179570149891903065806552272989075270143394417593863372800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_521 h,accepted_534 h⟩
private noncomputable def tree519 : TapeTree := .centered (candidateRows ibox519) (candidateRows (FixedTape.midBox ibox519))
attribute [irreducible] tree519
private theorem sign_519 : 2*denominator*(computed denominator (FixedTape.midBox ibox519)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox519).gradient k).lo.natAbs ((computed denominator ibox519).gradient k).hi.natAbs : Int)*((ibox519 k).hi-(ibox519 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox519
    (computed denominator ibox519) (computed denominator (FixedTape.midBox ibox519))
    (by decide +kernel)
private theorem midpoint_even_519 : ∀ k, 2 ∣ (ibox519 k).lo+(ibox519 k).hi := by decide +kernel
private theorem accepted_519 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox519) tree519 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox519 midpoint_even_519
  simp only [tree519,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox519,candidate_valid h (FixedTape.midBox ibox519),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox519 101 (FixedTape.rowsAux denominator ibox519 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox519) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_519
private noncomputable def tree518 : TapeTree := .centered (candidateRows ibox518) (candidateRows (FixedTape.midBox ibox518))
attribute [irreducible] tree518
private theorem sign_518 : 2*denominator*(computed denominator (FixedTape.midBox ibox518)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox518).gradient k).lo.natAbs ((computed denominator ibox518).gradient k).hi.natAbs : Int)*((ibox518 k).hi-(ibox518 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox518
    (computed denominator ibox518) (computed denominator (FixedTape.midBox ibox518))
    (by decide +kernel)
private theorem midpoint_even_518 : ∀ k, 2 ∣ (ibox518 k).lo+(ibox518 k).hi := by decide +kernel
private theorem accepted_518 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox518) tree518 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox518 midpoint_even_518
  simp only [tree518,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox518,candidate_valid h (FixedTape.midBox ibox518),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox518 101 (FixedTape.rowsAux denominator ibox518 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox518) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_518
private noncomputable def tree517 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree518 tree519
attribute [irreducible] tree517
private theorem accepted_517 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox517) tree517 = true := by
  simp only [tree517,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox517 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox517 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_518 h,accepted_519 h⟩
private noncomputable def tree516 : TapeTree := .centered (candidateRows ibox516) (candidateRows (FixedTape.midBox ibox516))
attribute [irreducible] tree516
private theorem sign_516 : 2*denominator*(computed denominator (FixedTape.midBox ibox516)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox516).gradient k).lo.natAbs ((computed denominator ibox516).gradient k).hi.natAbs : Int)*((ibox516 k).hi-(ibox516 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox516
    (computed denominator ibox516) (computed denominator (FixedTape.midBox ibox516))
    (by decide +kernel)
private theorem midpoint_even_516 : ∀ k, 2 ∣ (ibox516 k).lo+(ibox516 k).hi := by decide +kernel
private theorem accepted_516 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox516) tree516 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox516 midpoint_even_516
  simp only [tree516,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox516,candidate_valid h (FixedTape.midBox ibox516),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox516 101 (FixedTape.rowsAux denominator ibox516 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox516) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_516
private noncomputable def tree515 : TapeTree := .centered (candidateRows ibox515) (candidateRows (FixedTape.midBox ibox515))
attribute [irreducible] tree515
private theorem sign_515 : 2*denominator*(computed denominator (FixedTape.midBox ibox515)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox515).gradient k).lo.natAbs ((computed denominator ibox515).gradient k).hi.natAbs : Int)*((ibox515 k).hi-(ibox515 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox515
    (computed denominator ibox515) (computed denominator (FixedTape.midBox ibox515))
    (by decide +kernel)
private theorem midpoint_even_515 : ∀ k, 2 ∣ (ibox515 k).lo+(ibox515 k).hi := by decide +kernel
private theorem accepted_515 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox515) tree515 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox515 midpoint_even_515
  simp only [tree515,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox515,candidate_valid h (FixedTape.midBox ibox515),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox515 101 (FixedTape.rowsAux denominator ibox515 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox515) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_515
private noncomputable def tree514 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree515 tree516
attribute [irreducible] tree514
private theorem accepted_514 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox514) tree514 = true := by
  simp only [tree514,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox514 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox514 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_515 h,accepted_516 h⟩
private noncomputable def tree513 : TapeTree := .split 1 (((513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree514 tree517
attribute [irreducible] tree513
private theorem accepted_513 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox513) tree513 = true := by
  simp only [tree513,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox513 1 (513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 : Int) false,decode_split denominator ibox513 1 (513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_514 h,accepted_517 h⟩
private noncomputable def tree512 : TapeTree := .centered (candidateRows ibox512) (candidateRows (FixedTape.midBox ibox512))
attribute [irreducible] tree512
private theorem sign_512 : 2*denominator*(computed denominator (FixedTape.midBox ibox512)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox512).gradient k).lo.natAbs ((computed denominator ibox512).gradient k).hi.natAbs : Int)*((ibox512 k).hi-(ibox512 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox512
    (computed denominator ibox512) (computed denominator (FixedTape.midBox ibox512))
    (by decide +kernel)
private theorem midpoint_even_512 : ∀ k, 2 ∣ (ibox512 k).lo+(ibox512 k).hi := by decide +kernel
private theorem accepted_512 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox512) tree512 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox512 midpoint_even_512
  simp only [tree512,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox512,candidate_valid h (FixedTape.midBox ibox512),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox512 101 (FixedTape.rowsAux denominator ibox512 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox512) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_512
private noncomputable def tree511 : TapeTree := .centered (candidateRows ibox511) (candidateRows (FixedTape.midBox ibox511))
attribute [irreducible] tree511
private theorem sign_511 : 2*denominator*(computed denominator (FixedTape.midBox ibox511)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox511).gradient k).lo.natAbs ((computed denominator ibox511).gradient k).hi.natAbs : Int)*((ibox511 k).hi-(ibox511 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox511
    (computed denominator ibox511) (computed denominator (FixedTape.midBox ibox511))
    (by decide +kernel)
private theorem midpoint_even_511 : ∀ k, 2 ∣ (ibox511 k).lo+(ibox511 k).hi := by decide +kernel
private theorem accepted_511 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox511) tree511 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox511 midpoint_even_511
  simp only [tree511,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox511,candidate_valid h (FixedTape.midBox ibox511),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox511 101 (FixedTape.rowsAux denominator ibox511 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox511) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_511
private noncomputable def tree510 : TapeTree := .split 0 (((831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 : Int) : ℚ)/(denominator : ℚ)) tree511 tree512
attribute [irreducible] tree510
private theorem accepted_510 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox510) tree510 = true := by
  simp only [tree510,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox510 0 (831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 : Int) false,decode_split denominator ibox510 0 (831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_511 h,accepted_512 h⟩
private noncomputable def tree509 : TapeTree := .centered (candidateRows ibox509) (candidateRows (FixedTape.midBox ibox509))
attribute [irreducible] tree509
private theorem sign_509 : 2*denominator*(computed denominator (FixedTape.midBox ibox509)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox509).gradient k).lo.natAbs ((computed denominator ibox509).gradient k).hi.natAbs : Int)*((ibox509 k).hi-(ibox509 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox509
    (computed denominator ibox509) (computed denominator (FixedTape.midBox ibox509))
    (by decide +kernel)
private theorem midpoint_even_509 : ∀ k, 2 ∣ (ibox509 k).lo+(ibox509 k).hi := by decide +kernel
private theorem accepted_509 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox509) tree509 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox509 midpoint_even_509
  simp only [tree509,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox509,candidate_valid h (FixedTape.midBox ibox509),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox509 101 (FixedTape.rowsAux denominator ibox509 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox509) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_509
private noncomputable def tree508 : TapeTree := .centered (candidateRows ibox508) (candidateRows (FixedTape.midBox ibox508))
attribute [irreducible] tree508
private theorem sign_508 : 2*denominator*(computed denominator (FixedTape.midBox ibox508)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox508).gradient k).lo.natAbs ((computed denominator ibox508).gradient k).hi.natAbs : Int)*((ibox508 k).hi-(ibox508 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox508
    (computed denominator ibox508) (computed denominator (FixedTape.midBox ibox508))
    (by decide +kernel)
private theorem midpoint_even_508 : ∀ k, 2 ∣ (ibox508 k).lo+(ibox508 k).hi := by decide +kernel
private theorem accepted_508 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox508) tree508 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox508 midpoint_even_508
  simp only [tree508,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox508,candidate_valid h (FixedTape.midBox ibox508),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox508 101 (FixedTape.rowsAux denominator ibox508 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox508) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_508
private noncomputable def tree507 : TapeTree := .split 0 (((831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 : Int) : ℚ)/(denominator : ℚ)) tree508 tree509
attribute [irreducible] tree507
private theorem accepted_507 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox507) tree507 = true := by
  simp only [tree507,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox507 0 (831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 : Int) false,decode_split denominator ibox507 0 (831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_508 h,accepted_509 h⟩
private noncomputable def tree506 : TapeTree := .split 1 (((513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree507 tree510
attribute [irreducible] tree506
private theorem accepted_506 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox506) tree506 = true := by
  simp only [tree506,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox506 1 (513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 : Int) false,decode_split denominator ibox506 1 (513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_507 h,accepted_510 h⟩
private noncomputable def tree505 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree506 tree513
attribute [irreducible] tree505
private theorem accepted_505 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox505) tree505 = true := by
  simp only [tree505,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox505 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox505 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_506 h,accepted_513 h⟩
private noncomputable def tree504 : TapeTree := .centered (candidateRows ibox504) (candidateRows (FixedTape.midBox ibox504))
attribute [irreducible] tree504
private theorem sign_504 : 2*denominator*(computed denominator (FixedTape.midBox ibox504)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox504).gradient k).lo.natAbs ((computed denominator ibox504).gradient k).hi.natAbs : Int)*((ibox504 k).hi-(ibox504 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox504
    (computed denominator ibox504) (computed denominator (FixedTape.midBox ibox504))
    (by decide +kernel)
private theorem midpoint_even_504 : ∀ k, 2 ∣ (ibox504 k).lo+(ibox504 k).hi := by decide +kernel
private theorem accepted_504 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox504) tree504 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox504 midpoint_even_504
  simp only [tree504,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox504,candidate_valid h (FixedTape.midBox ibox504),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox504 101 (FixedTape.rowsAux denominator ibox504 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox504) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_504
private noncomputable def tree503 : TapeTree := .centered (candidateRows ibox503) (candidateRows (FixedTape.midBox ibox503))
attribute [irreducible] tree503
private theorem sign_503 : 2*denominator*(computed denominator (FixedTape.midBox ibox503)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox503).gradient k).lo.natAbs ((computed denominator ibox503).gradient k).hi.natAbs : Int)*((ibox503 k).hi-(ibox503 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox503
    (computed denominator ibox503) (computed denominator (FixedTape.midBox ibox503))
    (by decide +kernel)
private theorem midpoint_even_503 : ∀ k, 2 ∣ (ibox503 k).lo+(ibox503 k).hi := by decide +kernel
private theorem accepted_503 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox503) tree503 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox503 midpoint_even_503
  simp only [tree503,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox503,candidate_valid h (FixedTape.midBox ibox503),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox503 101 (FixedTape.rowsAux denominator ibox503 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox503) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_503
private noncomputable def tree502 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree503 tree504
attribute [irreducible] tree502
private theorem accepted_502 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox502) tree502 = true := by
  simp only [tree502,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox502 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox502 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_503 h,accepted_504 h⟩
private noncomputable def tree501 : TapeTree := .centered (candidateRows ibox501) (candidateRows (FixedTape.midBox ibox501))
attribute [irreducible] tree501
private theorem sign_501 : 2*denominator*(computed denominator (FixedTape.midBox ibox501)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox501).gradient k).lo.natAbs ((computed denominator ibox501).gradient k).hi.natAbs : Int)*((ibox501 k).hi-(ibox501 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox501
    (computed denominator ibox501) (computed denominator (FixedTape.midBox ibox501))
    (by decide +kernel)
private theorem midpoint_even_501 : ∀ k, 2 ∣ (ibox501 k).lo+(ibox501 k).hi := by decide +kernel
private theorem accepted_501 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox501) tree501 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox501 midpoint_even_501
  simp only [tree501,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox501,candidate_valid h (FixedTape.midBox ibox501),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox501 101 (FixedTape.rowsAux denominator ibox501 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox501) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_501
private noncomputable def tree500 : TapeTree := .centered (candidateRows ibox500) (candidateRows (FixedTape.midBox ibox500))
attribute [irreducible] tree500
private theorem sign_500 : 2*denominator*(computed denominator (FixedTape.midBox ibox500)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox500).gradient k).lo.natAbs ((computed denominator ibox500).gradient k).hi.natAbs : Int)*((ibox500 k).hi-(ibox500 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox500
    (computed denominator ibox500) (computed denominator (FixedTape.midBox ibox500))
    (by decide +kernel)
private theorem midpoint_even_500 : ∀ k, 2 ∣ (ibox500 k).lo+(ibox500 k).hi := by decide +kernel
private theorem accepted_500 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox500) tree500 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox500 midpoint_even_500
  simp only [tree500,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox500,candidate_valid h (FixedTape.midBox ibox500),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox500 101 (FixedTape.rowsAux denominator ibox500 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox500) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_500
private noncomputable def tree499 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree500 tree501
attribute [irreducible] tree499
private theorem accepted_499 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox499) tree499 = true := by
  simp only [tree499,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox499 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox499 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_500 h,accepted_501 h⟩
private noncomputable def tree498 : TapeTree := .split 1 (((459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree499 tree502
attribute [irreducible] tree498
private theorem accepted_498 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox498) tree498 = true := by
  simp only [tree498,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox498 1 (459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 : Int) false,decode_split denominator ibox498 1 (459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_499 h,accepted_502 h⟩
private noncomputable def tree497 : TapeTree := .centered (candidateRows ibox497) (candidateRows (FixedTape.midBox ibox497))
attribute [irreducible] tree497
private theorem sign_497 : 2*denominator*(computed denominator (FixedTape.midBox ibox497)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox497).gradient k).lo.natAbs ((computed denominator ibox497).gradient k).hi.natAbs : Int)*((ibox497 k).hi-(ibox497 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox497
    (computed denominator ibox497) (computed denominator (FixedTape.midBox ibox497))
    (by decide +kernel)
private theorem midpoint_even_497 : ∀ k, 2 ∣ (ibox497 k).lo+(ibox497 k).hi := by decide +kernel
private theorem accepted_497 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox497) tree497 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox497 midpoint_even_497
  simp only [tree497,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox497,candidate_valid h (FixedTape.midBox ibox497),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox497 101 (FixedTape.rowsAux denominator ibox497 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox497) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_497
private noncomputable def tree496 : TapeTree := .centered (candidateRows ibox496) (candidateRows (FixedTape.midBox ibox496))
attribute [irreducible] tree496
private theorem sign_496 : 2*denominator*(computed denominator (FixedTape.midBox ibox496)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox496).gradient k).lo.natAbs ((computed denominator ibox496).gradient k).hi.natAbs : Int)*((ibox496 k).hi-(ibox496 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox496
    (computed denominator ibox496) (computed denominator (FixedTape.midBox ibox496))
    (by decide +kernel)
private theorem midpoint_even_496 : ∀ k, 2 ∣ (ibox496 k).lo+(ibox496 k).hi := by decide +kernel
private theorem accepted_496 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox496) tree496 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox496 midpoint_even_496
  simp only [tree496,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox496,candidate_valid h (FixedTape.midBox ibox496),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox496 101 (FixedTape.rowsAux denominator ibox496 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox496) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_496
private noncomputable def tree495 : TapeTree := .split 0 (((831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 : Int) : ℚ)/(denominator : ℚ)) tree496 tree497
attribute [irreducible] tree495
private theorem accepted_495 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox495) tree495 = true := by
  simp only [tree495,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox495 0 (831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 : Int) false,decode_split denominator ibox495 0 (831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_496 h,accepted_497 h⟩
private noncomputable def tree494 : TapeTree := .centered (candidateRows ibox494) (candidateRows (FixedTape.midBox ibox494))
attribute [irreducible] tree494
private theorem sign_494 : 2*denominator*(computed denominator (FixedTape.midBox ibox494)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox494).gradient k).lo.natAbs ((computed denominator ibox494).gradient k).hi.natAbs : Int)*((ibox494 k).hi-(ibox494 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox494
    (computed denominator ibox494) (computed denominator (FixedTape.midBox ibox494))
    (by decide +kernel)
private theorem midpoint_even_494 : ∀ k, 2 ∣ (ibox494 k).lo+(ibox494 k).hi := by decide +kernel
private theorem accepted_494 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox494) tree494 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox494 midpoint_even_494
  simp only [tree494,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox494,candidate_valid h (FixedTape.midBox ibox494),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox494 101 (FixedTape.rowsAux denominator ibox494 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox494) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_494
private noncomputable def tree493 : TapeTree := .centered (candidateRows ibox493) (candidateRows (FixedTape.midBox ibox493))
attribute [irreducible] tree493
private theorem sign_493 : 2*denominator*(computed denominator (FixedTape.midBox ibox493)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox493).gradient k).lo.natAbs ((computed denominator ibox493).gradient k).hi.natAbs : Int)*((ibox493 k).hi-(ibox493 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox493
    (computed denominator ibox493) (computed denominator (FixedTape.midBox ibox493))
    (by decide +kernel)
private theorem midpoint_even_493 : ∀ k, 2 ∣ (ibox493 k).lo+(ibox493 k).hi := by decide +kernel
private theorem accepted_493 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox493) tree493 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox493 midpoint_even_493
  simp only [tree493,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox493,candidate_valid h (FixedTape.midBox ibox493),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox493 101 (FixedTape.rowsAux denominator ibox493 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox493) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_493
private noncomputable def tree492 : TapeTree := .split 0 (((831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 : Int) : ℚ)/(denominator : ℚ)) tree493 tree494
attribute [irreducible] tree492
private theorem accepted_492 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox492) tree492 = true := by
  simp only [tree492,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox492 0 (831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 : Int) false,decode_split denominator ibox492 0 (831560568894025146531015346980452766532828248134993063318869251442315592321279553699840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_493 h,accepted_494 h⟩
private noncomputable def tree491 : TapeTree := .split 1 (((459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree492 tree495
attribute [irreducible] tree491
private theorem accepted_491 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox491) tree491 = true := by
  simp only [tree491,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox491 1 (459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 : Int) false,decode_split denominator ibox491 1 (459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_492 h,accepted_495 h⟩
private noncomputable def tree490 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree491 tree498
attribute [irreducible] tree490
private theorem accepted_490 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox490) tree490 = true := by
  simp only [tree490,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox490 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox490 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_491 h,accepted_498 h⟩
private noncomputable def tree489 : TapeTree := .split 1 (((486767162279429328739213547920690205360950627425221026413614394979123200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree490 tree505
attribute [irreducible] tree489
private theorem accepted_489 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox489) tree489 = true := by
  simp only [tree489,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox489 1 (486767162279429328739213547920690205360950627425221026413614394979123200000000000000000000000 : Int) false,decode_split denominator ibox489 1 (486767162279429328739213547920690205360950627425221026413614394979123200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_490 h,accepted_505 h⟩
private noncomputable def tree488 : TapeTree := .split 1 (((540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree489 tree520
attribute [irreducible] tree488
private theorem accepted_488 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox488) tree488 = true := by
  simp only [tree488,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox488 1 (540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 : Int) false,decode_split denominator ibox488 1 (540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_489 h,accepted_520 h⟩
private noncomputable def tree487 : TapeTree := .split 1 (((649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree488 tree545
attribute [irreducible] tree487
private theorem accepted_487 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox487) tree487 = true := by
  simp only [tree487,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox487 1 (649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 : Int) false,decode_split denominator ibox487 1 (649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_488 h,accepted_545 h⟩
private noncomputable def tree486 : TapeTree := .centered (candidateRows ibox486) (candidateRows (FixedTape.midBox ibox486))
attribute [irreducible] tree486
private theorem sign_486 : 2*denominator*(computed denominator (FixedTape.midBox ibox486)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox486).gradient k).lo.natAbs ((computed denominator ibox486).gradient k).hi.natAbs : Int)*((ibox486 k).hi-(ibox486 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox486
    (computed denominator ibox486) (computed denominator (FixedTape.midBox ibox486))
    (by decide +kernel)
private theorem midpoint_even_486 : ∀ k, 2 ∣ (ibox486 k).lo+(ibox486 k).hi := by decide +kernel
private theorem accepted_486 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox486) tree486 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox486 midpoint_even_486
  simp only [tree486,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox486,candidate_valid h (FixedTape.midBox ibox486),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox486 101 (FixedTape.rowsAux denominator ibox486 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox486) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_486
private noncomputable def tree485 : TapeTree := .centered (candidateRows ibox485) (candidateRows (FixedTape.midBox ibox485))
attribute [irreducible] tree485
private theorem sign_485 : 2*denominator*(computed denominator (FixedTape.midBox ibox485)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox485).gradient k).lo.natAbs ((computed denominator ibox485).gradient k).hi.natAbs : Int)*((ibox485 k).hi-(ibox485 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox485
    (computed denominator ibox485) (computed denominator (FixedTape.midBox ibox485))
    (by decide +kernel)
private theorem midpoint_even_485 : ∀ k, 2 ∣ (ibox485 k).lo+(ibox485 k).hi := by decide +kernel
private theorem accepted_485 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox485) tree485 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox485 midpoint_even_485
  simp only [tree485,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox485,candidate_valid h (FixedTape.midBox ibox485),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox485 101 (FixedTape.rowsAux denominator ibox485 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox485) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_485
private noncomputable def tree484 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree485 tree486
attribute [irreducible] tree484
private theorem accepted_484 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox484) tree484 = true := by
  simp only [tree484,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox484 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox484 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_485 h,accepted_486 h⟩
private noncomputable def tree483 : TapeTree := .centered (candidateRows ibox483) (candidateRows (FixedTape.midBox ibox483))
attribute [irreducible] tree483
private theorem sign_483 : 2*denominator*(computed denominator (FixedTape.midBox ibox483)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox483).gradient k).lo.natAbs ((computed denominator ibox483).gradient k).hi.natAbs : Int)*((ibox483 k).hi-(ibox483 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox483
    (computed denominator ibox483) (computed denominator (FixedTape.midBox ibox483))
    (by decide +kernel)
private theorem midpoint_even_483 : ∀ k, 2 ∣ (ibox483 k).lo+(ibox483 k).hi := by decide +kernel
private theorem accepted_483 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox483) tree483 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox483 midpoint_even_483
  simp only [tree483,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox483,candidate_valid h (FixedTape.midBox ibox483),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox483 101 (FixedTape.rowsAux denominator ibox483 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox483) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_483
private noncomputable def tree482 : TapeTree := .centered (candidateRows ibox482) (candidateRows (FixedTape.midBox ibox482))
attribute [irreducible] tree482
private theorem sign_482 : 2*denominator*(computed denominator (FixedTape.midBox ibox482)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox482).gradient k).lo.natAbs ((computed denominator ibox482).gradient k).hi.natAbs : Int)*((ibox482 k).hi-(ibox482 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox482
    (computed denominator ibox482) (computed denominator (FixedTape.midBox ibox482))
    (by decide +kernel)
private theorem midpoint_even_482 : ∀ k, 2 ∣ (ibox482 k).lo+(ibox482 k).hi := by decide +kernel
private theorem accepted_482 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox482) tree482 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox482 midpoint_even_482
  simp only [tree482,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox482,candidate_valid h (FixedTape.midBox ibox482),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox482 101 (FixedTape.rowsAux denominator ibox482 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox482) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_482
private noncomputable def tree481 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree482 tree483
attribute [irreducible] tree481
private theorem accepted_481 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox481) tree481 = true := by
  simp only [tree481,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox481 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox481 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_482 h,accepted_483 h⟩
private noncomputable def tree480 : TapeTree := .split 1 (((405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree481 tree484
attribute [irreducible] tree480
private theorem accepted_480 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox480) tree480 = true := by
  simp only [tree480,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox480 1 (405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) false,decode_split denominator ibox480 1 (405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_481 h,accepted_484 h⟩
private noncomputable def tree479 : TapeTree := .centered (candidateRows ibox479) (candidateRows (FixedTape.midBox ibox479))
attribute [irreducible] tree479
private theorem sign_479 : 2*denominator*(computed denominator (FixedTape.midBox ibox479)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox479).gradient k).lo.natAbs ((computed denominator ibox479).gradient k).hi.natAbs : Int)*((ibox479 k).hi-(ibox479 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox479
    (computed denominator ibox479) (computed denominator (FixedTape.midBox ibox479))
    (by decide +kernel)
private theorem midpoint_even_479 : ∀ k, 2 ∣ (ibox479 k).lo+(ibox479 k).hi := by decide +kernel
private theorem accepted_479 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox479) tree479 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox479 midpoint_even_479
  simp only [tree479,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox479,candidate_valid h (FixedTape.midBox ibox479),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox479 101 (FixedTape.rowsAux denominator ibox479 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox479) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_479
private noncomputable def tree478 : TapeTree := .centered (candidateRows ibox478) (candidateRows (FixedTape.midBox ibox478))
attribute [irreducible] tree478
private theorem sign_478 : 2*denominator*(computed denominator (FixedTape.midBox ibox478)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox478).gradient k).lo.natAbs ((computed denominator ibox478).gradient k).hi.natAbs : Int)*((ibox478 k).hi-(ibox478 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox478
    (computed denominator ibox478) (computed denominator (FixedTape.midBox ibox478))
    (by decide +kernel)
private theorem midpoint_even_478 : ∀ k, 2 ∣ (ibox478 k).lo+(ibox478 k).hi := by decide +kernel
private theorem accepted_478 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox478) tree478 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox478 midpoint_even_478
  simp only [tree478,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox478,candidate_valid h (FixedTape.midBox ibox478),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox478 101 (FixedTape.rowsAux denominator ibox478 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox478) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_478
private noncomputable def tree477 : TapeTree := .split 1 (((405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree478 tree479
attribute [irreducible] tree477
private theorem accepted_477 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox477) tree477 = true := by
  simp only [tree477,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox477 1 (405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) false,decode_split denominator ibox477 1 (405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_478 h,accepted_479 h⟩
private noncomputable def tree476 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree477 tree480
attribute [irreducible] tree476
private theorem accepted_476 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox476) tree476 = true := by
  simp only [tree476,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox476 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox476 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_477 h,accepted_480 h⟩
private noncomputable def tree475 : TapeTree := .centered (candidateRows ibox475) (candidateRows (FixedTape.midBox ibox475))
attribute [irreducible] tree475
private theorem sign_475 : 2*denominator*(computed denominator (FixedTape.midBox ibox475)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox475).gradient k).lo.natAbs ((computed denominator ibox475).gradient k).hi.natAbs : Int)*((ibox475 k).hi-(ibox475 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox475
    (computed denominator ibox475) (computed denominator (FixedTape.midBox ibox475))
    (by decide +kernel)
private theorem midpoint_even_475 : ∀ k, 2 ∣ (ibox475 k).lo+(ibox475 k).hi := by decide +kernel
private theorem accepted_475 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox475) tree475 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox475 midpoint_even_475
  simp only [tree475,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox475,candidate_valid h (FixedTape.midBox ibox475),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox475 101 (FixedTape.rowsAux denominator ibox475 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox475) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_475
private noncomputable def tree474 : TapeTree := .centered (candidateRows ibox474) (candidateRows (FixedTape.midBox ibox474))
attribute [irreducible] tree474
private theorem sign_474 : 2*denominator*(computed denominator (FixedTape.midBox ibox474)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox474).gradient k).lo.natAbs ((computed denominator ibox474).gradient k).hi.natAbs : Int)*((ibox474 k).hi-(ibox474 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox474
    (computed denominator ibox474) (computed denominator (FixedTape.midBox ibox474))
    (by decide +kernel)
private theorem midpoint_even_474 : ∀ k, 2 ∣ (ibox474 k).lo+(ibox474 k).hi := by decide +kernel
private theorem accepted_474 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox474) tree474 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox474 midpoint_even_474
  simp only [tree474,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox474,candidate_valid h (FixedTape.midBox ibox474),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox474 101 (FixedTape.rowsAux denominator ibox474 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox474) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_474
private noncomputable def tree473 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree474 tree475
attribute [irreducible] tree473
private theorem accepted_473 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox473) tree473 = true := by
  simp only [tree473,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox473 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox473 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_474 h,accepted_475 h⟩
private noncomputable def tree472 : TapeTree := .centered (candidateRows ibox472) (candidateRows (FixedTape.midBox ibox472))
attribute [irreducible] tree472
private theorem sign_472 : 2*denominator*(computed denominator (FixedTape.midBox ibox472)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox472).gradient k).lo.natAbs ((computed denominator ibox472).gradient k).hi.natAbs : Int)*((ibox472 k).hi-(ibox472 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox472
    (computed denominator ibox472) (computed denominator (FixedTape.midBox ibox472))
    (by decide +kernel)
private theorem midpoint_even_472 : ∀ k, 2 ∣ (ibox472 k).lo+(ibox472 k).hi := by decide +kernel
private theorem accepted_472 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox472) tree472 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox472 midpoint_even_472
  simp only [tree472,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox472,candidate_valid h (FixedTape.midBox ibox472),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox472 101 (FixedTape.rowsAux denominator ibox472 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox472) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_472
private noncomputable def tree471 : TapeTree := .centered (candidateRows ibox471) (candidateRows (FixedTape.midBox ibox471))
attribute [irreducible] tree471
private theorem sign_471 : 2*denominator*(computed denominator (FixedTape.midBox ibox471)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox471).gradient k).lo.natAbs ((computed denominator ibox471).gradient k).hi.natAbs : Int)*((ibox471 k).hi-(ibox471 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox471
    (computed denominator ibox471) (computed denominator (FixedTape.midBox ibox471))
    (by decide +kernel)
private theorem midpoint_even_471 : ∀ k, 2 ∣ (ibox471 k).lo+(ibox471 k).hi := by decide +kernel
private theorem accepted_471 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox471) tree471 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox471 midpoint_even_471
  simp only [tree471,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox471,candidate_valid h (FixedTape.midBox ibox471),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox471 101 (FixedTape.rowsAux denominator ibox471 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox471) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_471
private noncomputable def tree470 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree471 tree472
attribute [irreducible] tree470
private theorem accepted_470 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox470) tree470 = true := by
  simp only [tree470,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox470 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox470 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_471 h,accepted_472 h⟩
private noncomputable def tree469 : TapeTree := .split 1 (((351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree470 tree473
attribute [irreducible] tree469
private theorem accepted_469 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox469) tree469 = true := by
  simp only [tree469,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox469 1 (351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) false,decode_split denominator ibox469 1 (351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_470 h,accepted_473 h⟩
private noncomputable def tree468 : TapeTree := .centered (candidateRows ibox468) (candidateRows (FixedTape.midBox ibox468))
attribute [irreducible] tree468
private theorem sign_468 : 2*denominator*(computed denominator (FixedTape.midBox ibox468)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox468).gradient k).lo.natAbs ((computed denominator ibox468).gradient k).hi.natAbs : Int)*((ibox468 k).hi-(ibox468 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox468
    (computed denominator ibox468) (computed denominator (FixedTape.midBox ibox468))
    (by decide +kernel)
private theorem midpoint_even_468 : ∀ k, 2 ∣ (ibox468 k).lo+(ibox468 k).hi := by decide +kernel
private theorem accepted_468 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox468) tree468 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox468 midpoint_even_468
  simp only [tree468,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox468,candidate_valid h (FixedTape.midBox ibox468),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox468 101 (FixedTape.rowsAux denominator ibox468 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox468) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_468
private noncomputable def tree467 : TapeTree := .centered (candidateRows ibox467) (candidateRows (FixedTape.midBox ibox467))
attribute [irreducible] tree467
private theorem sign_467 : 2*denominator*(computed denominator (FixedTape.midBox ibox467)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox467).gradient k).lo.natAbs ((computed denominator ibox467).gradient k).hi.natAbs : Int)*((ibox467 k).hi-(ibox467 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox467
    (computed denominator ibox467) (computed denominator (FixedTape.midBox ibox467))
    (by decide +kernel)
private theorem midpoint_even_467 : ∀ k, 2 ∣ (ibox467 k).lo+(ibox467 k).hi := by decide +kernel
private theorem accepted_467 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox467) tree467 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox467 midpoint_even_467
  simp only [tree467,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox467,candidate_valid h (FixedTape.midBox ibox467),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox467 101 (FixedTape.rowsAux denominator ibox467 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox467) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_467
private noncomputable def tree466 : TapeTree := .split 1 (((351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree467 tree468
attribute [irreducible] tree466
private theorem accepted_466 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox466) tree466 = true := by
  simp only [tree466,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox466 1 (351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) false,decode_split denominator ibox466 1 (351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_467 h,accepted_468 h⟩
private noncomputable def tree465 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree466 tree469
attribute [irreducible] tree465
private theorem accepted_465 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox465) tree465 = true := by
  simp only [tree465,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox465 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox465 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_466 h,accepted_469 h⟩
private noncomputable def tree464 : TapeTree := .split 1 (((378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree465 tree476
attribute [irreducible] tree464
private theorem accepted_464 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox464) tree464 = true := by
  simp only [tree464,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox464 1 (378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 : Int) false,decode_split denominator ibox464 1 (378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_465 h,accepted_476 h⟩
private noncomputable def tree463 : TapeTree := .centered (candidateRows ibox463) (candidateRows (FixedTape.midBox ibox463))
attribute [irreducible] tree463
private theorem sign_463 : 2*denominator*(computed denominator (FixedTape.midBox ibox463)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox463).gradient k).lo.natAbs ((computed denominator ibox463).gradient k).hi.natAbs : Int)*((ibox463 k).hi-(ibox463 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox463
    (computed denominator ibox463) (computed denominator (FixedTape.midBox ibox463))
    (by decide +kernel)
private theorem midpoint_even_463 : ∀ k, 2 ∣ (ibox463 k).lo+(ibox463 k).hi := by decide +kernel
private theorem accepted_463 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox463) tree463 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox463 midpoint_even_463
  simp only [tree463,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox463,candidate_valid h (FixedTape.midBox ibox463),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox463 101 (FixedTape.rowsAux denominator ibox463 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox463) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_463
private noncomputable def tree462 : TapeTree := .centered (candidateRows ibox462) (candidateRows (FixedTape.midBox ibox462))
attribute [irreducible] tree462
private theorem sign_462 : 2*denominator*(computed denominator (FixedTape.midBox ibox462)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox462).gradient k).lo.natAbs ((computed denominator ibox462).gradient k).hi.natAbs : Int)*((ibox462 k).hi-(ibox462 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox462
    (computed denominator ibox462) (computed denominator (FixedTape.midBox ibox462))
    (by decide +kernel)
private theorem midpoint_even_462 : ∀ k, 2 ∣ (ibox462 k).lo+(ibox462 k).hi := by decide +kernel
private theorem accepted_462 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox462) tree462 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox462 midpoint_even_462
  simp only [tree462,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox462,candidate_valid h (FixedTape.midBox ibox462),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox462 101 (FixedTape.rowsAux denominator ibox462 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox462) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_462
private noncomputable def tree461 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree462 tree463
attribute [irreducible] tree461
private theorem accepted_461 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox461) tree461 = true := by
  simp only [tree461,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox461 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox461 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_462 h,accepted_463 h⟩
private noncomputable def tree460 : TapeTree := .centered (candidateRows ibox460) (candidateRows (FixedTape.midBox ibox460))
attribute [irreducible] tree460
private theorem sign_460 : 2*denominator*(computed denominator (FixedTape.midBox ibox460)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox460).gradient k).lo.natAbs ((computed denominator ibox460).gradient k).hi.natAbs : Int)*((ibox460 k).hi-(ibox460 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox460
    (computed denominator ibox460) (computed denominator (FixedTape.midBox ibox460))
    (by decide +kernel)
private theorem midpoint_even_460 : ∀ k, 2 ∣ (ibox460 k).lo+(ibox460 k).hi := by decide +kernel
private theorem accepted_460 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox460) tree460 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox460 midpoint_even_460
  simp only [tree460,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox460,candidate_valid h (FixedTape.midBox ibox460),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox460 101 (FixedTape.rowsAux denominator ibox460 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox460) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_460
private noncomputable def tree459 : TapeTree := .centered (candidateRows ibox459) (candidateRows (FixedTape.midBox ibox459))
attribute [irreducible] tree459
private theorem sign_459 : 2*denominator*(computed denominator (FixedTape.midBox ibox459)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox459).gradient k).lo.natAbs ((computed denominator ibox459).gradient k).hi.natAbs : Int)*((ibox459 k).hi-(ibox459 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox459
    (computed denominator ibox459) (computed denominator (FixedTape.midBox ibox459))
    (by decide +kernel)
private theorem midpoint_even_459 : ∀ k, 2 ∣ (ibox459 k).lo+(ibox459 k).hi := by decide +kernel
private theorem accepted_459 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox459) tree459 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox459 midpoint_even_459
  simp only [tree459,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox459,candidate_valid h (FixedTape.midBox ibox459),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox459 101 (FixedTape.rowsAux denominator ibox459 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox459) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_459
private noncomputable def tree458 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree459 tree460
attribute [irreducible] tree458
private theorem accepted_458 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox458) tree458 = true := by
  simp only [tree458,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox458 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox458 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_459 h,accepted_460 h⟩
private noncomputable def tree457 : TapeTree := .split 1 (((297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree458 tree461
attribute [irreducible] tree457
private theorem accepted_457 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox457) tree457 = true := by
  simp only [tree457,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox457 1 (297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) false,decode_split denominator ibox457 1 (297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_458 h,accepted_461 h⟩
private noncomputable def tree456 : TapeTree := .centered (candidateRows ibox456) (candidateRows (FixedTape.midBox ibox456))
attribute [irreducible] tree456
private theorem sign_456 : 2*denominator*(computed denominator (FixedTape.midBox ibox456)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox456).gradient k).lo.natAbs ((computed denominator ibox456).gradient k).hi.natAbs : Int)*((ibox456 k).hi-(ibox456 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox456
    (computed denominator ibox456) (computed denominator (FixedTape.midBox ibox456))
    (by decide +kernel)
private theorem midpoint_even_456 : ∀ k, 2 ∣ (ibox456 k).lo+(ibox456 k).hi := by decide +kernel
private theorem accepted_456 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox456) tree456 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox456 midpoint_even_456
  simp only [tree456,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox456,candidate_valid h (FixedTape.midBox ibox456),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox456 101 (FixedTape.rowsAux denominator ibox456 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox456) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_456
private noncomputable def tree455 : TapeTree := .centered (candidateRows ibox455) (candidateRows (FixedTape.midBox ibox455))
attribute [irreducible] tree455
private theorem sign_455 : 2*denominator*(computed denominator (FixedTape.midBox ibox455)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox455).gradient k).lo.natAbs ((computed denominator ibox455).gradient k).hi.natAbs : Int)*((ibox455 k).hi-(ibox455 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox455
    (computed denominator ibox455) (computed denominator (FixedTape.midBox ibox455))
    (by decide +kernel)
private theorem midpoint_even_455 : ∀ k, 2 ∣ (ibox455 k).lo+(ibox455 k).hi := by decide +kernel
private theorem accepted_455 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox455) tree455 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox455 midpoint_even_455
  simp only [tree455,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox455,candidate_valid h (FixedTape.midBox ibox455),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox455 101 (FixedTape.rowsAux denominator ibox455 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox455) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_455
private noncomputable def tree454 : TapeTree := .split 1 (((297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree455 tree456
attribute [irreducible] tree454
private theorem accepted_454 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox454) tree454 = true := by
  simp only [tree454,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox454 1 (297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) false,decode_split denominator ibox454 1 (297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_455 h,accepted_456 h⟩
private noncomputable def tree453 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree454 tree457
attribute [irreducible] tree453
private theorem accepted_453 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox453) tree453 = true := by
  simp only [tree453,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox453 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox453 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_454 h,accepted_457 h⟩
private noncomputable def tree452 : TapeTree := .centered (candidateRows ibox452) (candidateRows (FixedTape.midBox ibox452))
attribute [irreducible] tree452
private theorem sign_452 : 2*denominator*(computed denominator (FixedTape.midBox ibox452)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox452).gradient k).lo.natAbs ((computed denominator ibox452).gradient k).hi.natAbs : Int)*((ibox452 k).hi-(ibox452 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox452
    (computed denominator ibox452) (computed denominator (FixedTape.midBox ibox452))
    (by decide +kernel)
private theorem midpoint_even_452 : ∀ k, 2 ∣ (ibox452 k).lo+(ibox452 k).hi := by decide +kernel
private theorem accepted_452 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox452) tree452 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox452 midpoint_even_452
  simp only [tree452,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox452,candidate_valid h (FixedTape.midBox ibox452),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox452 101 (FixedTape.rowsAux denominator ibox452 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox452) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_452
private noncomputable def tree451 : TapeTree := .centered (candidateRows ibox451) (candidateRows (FixedTape.midBox ibox451))
attribute [irreducible] tree451
private theorem sign_451 : 2*denominator*(computed denominator (FixedTape.midBox ibox451)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox451).gradient k).lo.natAbs ((computed denominator ibox451).gradient k).hi.natAbs : Int)*((ibox451 k).hi-(ibox451 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox451
    (computed denominator ibox451) (computed denominator (FixedTape.midBox ibox451))
    (by decide +kernel)
private theorem midpoint_even_451 : ∀ k, 2 ∣ (ibox451 k).lo+(ibox451 k).hi := by decide +kernel
private theorem accepted_451 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox451) tree451 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox451 midpoint_even_451
  simp only [tree451,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox451,candidate_valid h (FixedTape.midBox ibox451),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox451 101 (FixedTape.rowsAux denominator ibox451 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox451) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_451
private noncomputable def tree450 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree451 tree452
attribute [irreducible] tree450
private theorem accepted_450 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox450) tree450 = true := by
  simp only [tree450,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox450 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox450 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_451 h,accepted_452 h⟩
private noncomputable def tree449 : TapeTree := .centered (candidateRows ibox449) (candidateRows (FixedTape.midBox ibox449))
attribute [irreducible] tree449
private theorem sign_449 : 2*denominator*(computed denominator (FixedTape.midBox ibox449)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox449).gradient k).lo.natAbs ((computed denominator ibox449).gradient k).hi.natAbs : Int)*((ibox449 k).hi-(ibox449 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox449
    (computed denominator ibox449) (computed denominator (FixedTape.midBox ibox449))
    (by decide +kernel)
private theorem midpoint_even_449 : ∀ k, 2 ∣ (ibox449 k).lo+(ibox449 k).hi := by decide +kernel
private theorem accepted_449 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox449) tree449 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox449 midpoint_even_449
  simp only [tree449,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox449,candidate_valid h (FixedTape.midBox ibox449),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox449 101 (FixedTape.rowsAux denominator ibox449 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox449) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_449
private noncomputable def tree448 : TapeTree := .centered (candidateRows ibox448) (candidateRows (FixedTape.midBox ibox448))
attribute [irreducible] tree448
private theorem sign_448 : 2*denominator*(computed denominator (FixedTape.midBox ibox448)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox448).gradient k).lo.natAbs ((computed denominator ibox448).gradient k).hi.natAbs : Int)*((ibox448 k).hi-(ibox448 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox448
    (computed denominator ibox448) (computed denominator (FixedTape.midBox ibox448))
    (by decide +kernel)
private theorem midpoint_even_448 : ∀ k, 2 ∣ (ibox448 k).lo+(ibox448 k).hi := by decide +kernel
private theorem accepted_448 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox448) tree448 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox448 midpoint_even_448
  simp only [tree448,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox448,candidate_valid h (FixedTape.midBox ibox448),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox448 101 (FixedTape.rowsAux denominator ibox448 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox448) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_448
private noncomputable def tree447 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree448 tree449
attribute [irreducible] tree447
private theorem accepted_447 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox447) tree447 = true := by
  simp only [tree447,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox447 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox447 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_448 h,accepted_449 h⟩
private noncomputable def tree446 : TapeTree := .split 1 (((243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree447 tree450
attribute [irreducible] tree446
private theorem accepted_446 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox446) tree446 = true := by
  simp only [tree446,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox446 1 (243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) false,decode_split denominator ibox446 1 (243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_447 h,accepted_450 h⟩
private noncomputable def tree445 : TapeTree := .centered (candidateRows ibox445) (candidateRows (FixedTape.midBox ibox445))
attribute [irreducible] tree445
private theorem sign_445 : 2*denominator*(computed denominator (FixedTape.midBox ibox445)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox445).gradient k).lo.natAbs ((computed denominator ibox445).gradient k).hi.natAbs : Int)*((ibox445 k).hi-(ibox445 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox445
    (computed denominator ibox445) (computed denominator (FixedTape.midBox ibox445))
    (by decide +kernel)
private theorem midpoint_even_445 : ∀ k, 2 ∣ (ibox445 k).lo+(ibox445 k).hi := by decide +kernel
private theorem accepted_445 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox445) tree445 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox445 midpoint_even_445
  simp only [tree445,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox445,candidate_valid h (FixedTape.midBox ibox445),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox445 101 (FixedTape.rowsAux denominator ibox445 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox445) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_445
private noncomputable def tree444 : TapeTree := .centered (candidateRows ibox444) (candidateRows (FixedTape.midBox ibox444))
attribute [irreducible] tree444
private theorem sign_444 : 2*denominator*(computed denominator (FixedTape.midBox ibox444)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox444).gradient k).lo.natAbs ((computed denominator ibox444).gradient k).hi.natAbs : Int)*((ibox444 k).hi-(ibox444 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox444
    (computed denominator ibox444) (computed denominator (FixedTape.midBox ibox444))
    (by decide +kernel)
private theorem midpoint_even_444 : ∀ k, 2 ∣ (ibox444 k).lo+(ibox444 k).hi := by decide +kernel
private theorem accepted_444 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox444) tree444 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox444 midpoint_even_444
  simp only [tree444,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox444,candidate_valid h (FixedTape.midBox ibox444),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox444 101 (FixedTape.rowsAux denominator ibox444 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox444) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_444
private noncomputable def tree443 : TapeTree := .split 1 (((243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree444 tree445
attribute [irreducible] tree443
private theorem accepted_443 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox443) tree443 = true := by
  simp only [tree443,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox443 1 (243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) false,decode_split denominator ibox443 1 (243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_444 h,accepted_445 h⟩
private noncomputable def tree442 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree443 tree446
attribute [irreducible] tree442
private theorem accepted_442 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox442) tree442 = true := by
  simp only [tree442,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox442 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox442 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_443 h,accepted_446 h⟩
private noncomputable def tree441 : TapeTree := .split 1 (((270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree442 tree453
attribute [irreducible] tree441
private theorem accepted_441 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox441) tree441 = true := by
  simp only [tree441,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox441 1 (270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 : Int) false,decode_split denominator ibox441 1 (270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_442 h,accepted_453 h⟩
private noncomputable def tree440 : TapeTree := .split 1 (((324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree441 tree464
attribute [irreducible] tree440
private theorem accepted_440 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox440) tree440 = true := by
  simp only [tree440,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox440 1 (324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 : Int) false,decode_split denominator ibox440 1 (324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_441 h,accepted_464 h⟩
private noncomputable def tree439 : TapeTree := .centered (candidateRows ibox439) (candidateRows (FixedTape.midBox ibox439))
attribute [irreducible] tree439
private theorem sign_439 : 2*denominator*(computed denominator (FixedTape.midBox ibox439)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox439).gradient k).lo.natAbs ((computed denominator ibox439).gradient k).hi.natAbs : Int)*((ibox439 k).hi-(ibox439 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox439
    (computed denominator ibox439) (computed denominator (FixedTape.midBox ibox439))
    (by decide +kernel)
private theorem midpoint_even_439 : ∀ k, 2 ∣ (ibox439 k).lo+(ibox439 k).hi := by decide +kernel
private theorem accepted_439 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox439) tree439 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox439 midpoint_even_439
  simp only [tree439,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox439,candidate_valid h (FixedTape.midBox ibox439),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox439 101 (FixedTape.rowsAux denominator ibox439 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox439) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_439
private noncomputable def tree438 : TapeTree := .centered (candidateRows ibox438) (candidateRows (FixedTape.midBox ibox438))
attribute [irreducible] tree438
private theorem sign_438 : 2*denominator*(computed denominator (FixedTape.midBox ibox438)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox438).gradient k).lo.natAbs ((computed denominator ibox438).gradient k).hi.natAbs : Int)*((ibox438 k).hi-(ibox438 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox438
    (computed denominator ibox438) (computed denominator (FixedTape.midBox ibox438))
    (by decide +kernel)
private theorem midpoint_even_438 : ∀ k, 2 ∣ (ibox438 k).lo+(ibox438 k).hi := by decide +kernel
private theorem accepted_438 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox438) tree438 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox438 midpoint_even_438
  simp only [tree438,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox438,candidate_valid h (FixedTape.midBox ibox438),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox438 101 (FixedTape.rowsAux denominator ibox438 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox438) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_438
private noncomputable def tree437 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree438 tree439
attribute [irreducible] tree437
private theorem accepted_437 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox437) tree437 = true := by
  simp only [tree437,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox437 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox437 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_438 h,accepted_439 h⟩
private noncomputable def tree436 : TapeTree := .centered (candidateRows ibox436) (candidateRows (FixedTape.midBox ibox436))
attribute [irreducible] tree436
private theorem sign_436 : 2*denominator*(computed denominator (FixedTape.midBox ibox436)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox436).gradient k).lo.natAbs ((computed denominator ibox436).gradient k).hi.natAbs : Int)*((ibox436 k).hi-(ibox436 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox436
    (computed denominator ibox436) (computed denominator (FixedTape.midBox ibox436))
    (by decide +kernel)
private theorem midpoint_even_436 : ∀ k, 2 ∣ (ibox436 k).lo+(ibox436 k).hi := by decide +kernel
private theorem accepted_436 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox436) tree436 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox436 midpoint_even_436
  simp only [tree436,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox436,candidate_valid h (FixedTape.midBox ibox436),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox436 101 (FixedTape.rowsAux denominator ibox436 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox436) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_436
private noncomputable def tree435 : TapeTree := .centered (candidateRows ibox435) (candidateRows (FixedTape.midBox ibox435))
attribute [irreducible] tree435
private theorem sign_435 : 2*denominator*(computed denominator (FixedTape.midBox ibox435)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox435).gradient k).lo.natAbs ((computed denominator ibox435).gradient k).hi.natAbs : Int)*((ibox435 k).hi-(ibox435 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox435
    (computed denominator ibox435) (computed denominator (FixedTape.midBox ibox435))
    (by decide +kernel)
private theorem midpoint_even_435 : ∀ k, 2 ∣ (ibox435 k).lo+(ibox435 k).hi := by decide +kernel
private theorem accepted_435 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox435) tree435 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox435 midpoint_even_435
  simp only [tree435,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox435,candidate_valid h (FixedTape.midBox ibox435),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox435 101 (FixedTape.rowsAux denominator ibox435 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox435) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_435
private noncomputable def tree434 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree435 tree436
attribute [irreducible] tree434
private theorem accepted_434 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox434) tree434 = true := by
  simp only [tree434,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox434 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox434 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_435 h,accepted_436 h⟩
private noncomputable def tree433 : TapeTree := .split 1 (((189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree434 tree437
attribute [irreducible] tree433
private theorem accepted_433 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox433) tree433 = true := by
  simp only [tree433,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox433 1 (189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) false,decode_split denominator ibox433 1 (189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_434 h,accepted_437 h⟩
private noncomputable def tree432 : TapeTree := .centered (candidateRows ibox432) (candidateRows (FixedTape.midBox ibox432))
attribute [irreducible] tree432
private theorem sign_432 : 2*denominator*(computed denominator (FixedTape.midBox ibox432)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox432).gradient k).lo.natAbs ((computed denominator ibox432).gradient k).hi.natAbs : Int)*((ibox432 k).hi-(ibox432 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox432
    (computed denominator ibox432) (computed denominator (FixedTape.midBox ibox432))
    (by decide +kernel)
private theorem midpoint_even_432 : ∀ k, 2 ∣ (ibox432 k).lo+(ibox432 k).hi := by decide +kernel
private theorem accepted_432 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox432) tree432 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox432 midpoint_even_432
  simp only [tree432,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox432,candidate_valid h (FixedTape.midBox ibox432),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox432 101 (FixedTape.rowsAux denominator ibox432 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox432) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_432
private noncomputable def tree431 : TapeTree := .centered (candidateRows ibox431) (candidateRows (FixedTape.midBox ibox431))
attribute [irreducible] tree431
private theorem sign_431 : 2*denominator*(computed denominator (FixedTape.midBox ibox431)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox431).gradient k).lo.natAbs ((computed denominator ibox431).gradient k).hi.natAbs : Int)*((ibox431 k).hi-(ibox431 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox431
    (computed denominator ibox431) (computed denominator (FixedTape.midBox ibox431))
    (by decide +kernel)
private theorem midpoint_even_431 : ∀ k, 2 ∣ (ibox431 k).lo+(ibox431 k).hi := by decide +kernel
private theorem accepted_431 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox431) tree431 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox431 midpoint_even_431
  simp only [tree431,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox431,candidate_valid h (FixedTape.midBox ibox431),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox431 101 (FixedTape.rowsAux denominator ibox431 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox431) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_431
private noncomputable def tree430 : TapeTree := .split 1 (((189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree431 tree432
attribute [irreducible] tree430
private theorem accepted_430 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox430) tree430 = true := by
  simp only [tree430,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox430 1 (189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) false,decode_split denominator ibox430 1 (189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_431 h,accepted_432 h⟩
private noncomputable def tree429 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree430 tree433
attribute [irreducible] tree429
private theorem accepted_429 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox429) tree429 = true := by
  simp only [tree429,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox429 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox429 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_430 h,accepted_433 h⟩
private noncomputable def tree428 : TapeTree := .centered (candidateRows ibox428) (candidateRows (FixedTape.midBox ibox428))
attribute [irreducible] tree428
private theorem sign_428 : 2*denominator*(computed denominator (FixedTape.midBox ibox428)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox428).gradient k).lo.natAbs ((computed denominator ibox428).gradient k).hi.natAbs : Int)*((ibox428 k).hi-(ibox428 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox428
    (computed denominator ibox428) (computed denominator (FixedTape.midBox ibox428))
    (by decide +kernel)
private theorem midpoint_even_428 : ∀ k, 2 ∣ (ibox428 k).lo+(ibox428 k).hi := by decide +kernel
private theorem accepted_428 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox428) tree428 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox428 midpoint_even_428
  simp only [tree428,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox428,candidate_valid h (FixedTape.midBox ibox428),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox428 101 (FixedTape.rowsAux denominator ibox428 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox428) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_428
private noncomputable def tree427 : TapeTree := .centered (candidateRows ibox427) (candidateRows (FixedTape.midBox ibox427))
attribute [irreducible] tree427
private theorem sign_427 : 2*denominator*(computed denominator (FixedTape.midBox ibox427)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox427).gradient k).lo.natAbs ((computed denominator ibox427).gradient k).hi.natAbs : Int)*((ibox427 k).hi-(ibox427 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox427
    (computed denominator ibox427) (computed denominator (FixedTape.midBox ibox427))
    (by decide +kernel)
private theorem midpoint_even_427 : ∀ k, 2 ∣ (ibox427 k).lo+(ibox427 k).hi := by decide +kernel
private theorem accepted_427 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox427) tree427 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox427 midpoint_even_427
  simp only [tree427,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox427,candidate_valid h (FixedTape.midBox ibox427),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox427 101 (FixedTape.rowsAux denominator ibox427 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox427) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_427
private noncomputable def tree426 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree427 tree428
attribute [irreducible] tree426
private theorem accepted_426 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox426) tree426 = true := by
  simp only [tree426,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox426 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox426 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_427 h,accepted_428 h⟩
private noncomputable def tree425 : TapeTree := .centered (candidateRows ibox425) (candidateRows (FixedTape.midBox ibox425))
attribute [irreducible] tree425
private theorem sign_425 : 2*denominator*(computed denominator (FixedTape.midBox ibox425)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox425).gradient k).lo.natAbs ((computed denominator ibox425).gradient k).hi.natAbs : Int)*((ibox425 k).hi-(ibox425 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox425
    (computed denominator ibox425) (computed denominator (FixedTape.midBox ibox425))
    (by decide +kernel)
private theorem midpoint_even_425 : ∀ k, 2 ∣ (ibox425 k).lo+(ibox425 k).hi := by decide +kernel
private theorem accepted_425 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox425) tree425 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox425 midpoint_even_425
  simp only [tree425,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox425,candidate_valid h (FixedTape.midBox ibox425),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox425 101 (FixedTape.rowsAux denominator ibox425 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox425) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_425
private noncomputable def tree424 : TapeTree := .centered (candidateRows ibox424) (candidateRows (FixedTape.midBox ibox424))
attribute [irreducible] tree424
private theorem sign_424 : 2*denominator*(computed denominator (FixedTape.midBox ibox424)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox424).gradient k).lo.natAbs ((computed denominator ibox424).gradient k).hi.natAbs : Int)*((ibox424 k).hi-(ibox424 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox424
    (computed denominator ibox424) (computed denominator (FixedTape.midBox ibox424))
    (by decide +kernel)
private theorem midpoint_even_424 : ∀ k, 2 ∣ (ibox424 k).lo+(ibox424 k).hi := by decide +kernel
private theorem accepted_424 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox424) tree424 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox424 midpoint_even_424
  simp only [tree424,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox424,candidate_valid h (FixedTape.midBox ibox424),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox424 101 (FixedTape.rowsAux denominator ibox424 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox424) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_424
private noncomputable def tree423 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree424 tree425
attribute [irreducible] tree423
private theorem accepted_423 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox423) tree423 = true := by
  simp only [tree423,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox423 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox423 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_424 h,accepted_425 h⟩
private noncomputable def tree422 : TapeTree := .split 1 (((135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree423 tree426
attribute [irreducible] tree422
private theorem accepted_422 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox422) tree422 = true := by
  simp only [tree422,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox422 1 (135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) false,decode_split denominator ibox422 1 (135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_423 h,accepted_426 h⟩
private noncomputable def tree421 : TapeTree := .centered (candidateRows ibox421) (candidateRows (FixedTape.midBox ibox421))
attribute [irreducible] tree421
private theorem sign_421 : 2*denominator*(computed denominator (FixedTape.midBox ibox421)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox421).gradient k).lo.natAbs ((computed denominator ibox421).gradient k).hi.natAbs : Int)*((ibox421 k).hi-(ibox421 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox421
    (computed denominator ibox421) (computed denominator (FixedTape.midBox ibox421))
    (by decide +kernel)
private theorem midpoint_even_421 : ∀ k, 2 ∣ (ibox421 k).lo+(ibox421 k).hi := by decide +kernel
private theorem accepted_421 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox421) tree421 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox421 midpoint_even_421
  simp only [tree421,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox421,candidate_valid h (FixedTape.midBox ibox421),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox421 101 (FixedTape.rowsAux denominator ibox421 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox421) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_421
private noncomputable def tree420 : TapeTree := .centered (candidateRows ibox420) (candidateRows (FixedTape.midBox ibox420))
attribute [irreducible] tree420
private theorem sign_420 : 2*denominator*(computed denominator (FixedTape.midBox ibox420)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox420).gradient k).lo.natAbs ((computed denominator ibox420).gradient k).hi.natAbs : Int)*((ibox420 k).hi-(ibox420 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox420
    (computed denominator ibox420) (computed denominator (FixedTape.midBox ibox420))
    (by decide +kernel)
private theorem midpoint_even_420 : ∀ k, 2 ∣ (ibox420 k).lo+(ibox420 k).hi := by decide +kernel
private theorem accepted_420 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox420) tree420 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox420 midpoint_even_420
  simp only [tree420,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox420,candidate_valid h (FixedTape.midBox ibox420),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox420 101 (FixedTape.rowsAux denominator ibox420 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox420) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_420
private noncomputable def tree419 : TapeTree := .split 1 (((135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree420 tree421
attribute [irreducible] tree419
private theorem accepted_419 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox419) tree419 = true := by
  simp only [tree419,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox419 1 (135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) false,decode_split denominator ibox419 1 (135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_420 h,accepted_421 h⟩
private noncomputable def tree418 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree419 tree422
attribute [irreducible] tree418
private theorem accepted_418 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox418) tree418 = true := by
  simp only [tree418,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox418 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox418 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_419 h,accepted_422 h⟩
private noncomputable def tree417 : TapeTree := .split 1 (((162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree418 tree429
attribute [irreducible] tree417
private theorem accepted_417 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox417) tree417 = true := by
  simp only [tree417,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox417 1 (162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 : Int) false,decode_split denominator ibox417 1 (162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_418 h,accepted_429 h⟩
private noncomputable def tree416 : TapeTree := .centered (candidateRows ibox416) (candidateRows (FixedTape.midBox ibox416))
attribute [irreducible] tree416
private theorem sign_416 : 2*denominator*(computed denominator (FixedTape.midBox ibox416)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox416).gradient k).lo.natAbs ((computed denominator ibox416).gradient k).hi.natAbs : Int)*((ibox416 k).hi-(ibox416 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox416
    (computed denominator ibox416) (computed denominator (FixedTape.midBox ibox416))
    (by decide +kernel)
private theorem midpoint_even_416 : ∀ k, 2 ∣ (ibox416 k).lo+(ibox416 k).hi := by decide +kernel
private theorem accepted_416 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox416) tree416 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox416 midpoint_even_416
  simp only [tree416,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox416,candidate_valid h (FixedTape.midBox ibox416),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox416 101 (FixedTape.rowsAux denominator ibox416 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox416) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_416
private noncomputable def tree415 : TapeTree := .centered (candidateRows ibox415) (candidateRows (FixedTape.midBox ibox415))
attribute [irreducible] tree415
private theorem sign_415 : 2*denominator*(computed denominator (FixedTape.midBox ibox415)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox415).gradient k).lo.natAbs ((computed denominator ibox415).gradient k).hi.natAbs : Int)*((ibox415 k).hi-(ibox415 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox415
    (computed denominator ibox415) (computed denominator (FixedTape.midBox ibox415))
    (by decide +kernel)
private theorem midpoint_even_415 : ∀ k, 2 ∣ (ibox415 k).lo+(ibox415 k).hi := by decide +kernel
private theorem accepted_415 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox415) tree415 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox415 midpoint_even_415
  simp only [tree415,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox415,candidate_valid h (FixedTape.midBox ibox415),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox415 101 (FixedTape.rowsAux denominator ibox415 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox415) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_415
private noncomputable def tree414 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree415 tree416
attribute [irreducible] tree414
private theorem accepted_414 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox414) tree414 = true := by
  simp only [tree414,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox414 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox414 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_415 h,accepted_416 h⟩
private noncomputable def tree413 : TapeTree := .centered (candidateRows ibox413) (candidateRows (FixedTape.midBox ibox413))
attribute [irreducible] tree413
private theorem sign_413 : 2*denominator*(computed denominator (FixedTape.midBox ibox413)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox413).gradient k).lo.natAbs ((computed denominator ibox413).gradient k).hi.natAbs : Int)*((ibox413 k).hi-(ibox413 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox413
    (computed denominator ibox413) (computed denominator (FixedTape.midBox ibox413))
    (by decide +kernel)
private theorem midpoint_even_413 : ∀ k, 2 ∣ (ibox413 k).lo+(ibox413 k).hi := by decide +kernel
private theorem accepted_413 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox413) tree413 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox413 midpoint_even_413
  simp only [tree413,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox413,candidate_valid h (FixedTape.midBox ibox413),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox413 101 (FixedTape.rowsAux denominator ibox413 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox413) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_413
private noncomputable def tree412 : TapeTree := .centered (candidateRows ibox412) (candidateRows (FixedTape.midBox ibox412))
attribute [irreducible] tree412
private theorem sign_412 : 2*denominator*(computed denominator (FixedTape.midBox ibox412)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox412).gradient k).lo.natAbs ((computed denominator ibox412).gradient k).hi.natAbs : Int)*((ibox412 k).hi-(ibox412 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox412
    (computed denominator ibox412) (computed denominator (FixedTape.midBox ibox412))
    (by decide +kernel)
private theorem midpoint_even_412 : ∀ k, 2 ∣ (ibox412 k).lo+(ibox412 k).hi := by decide +kernel
private theorem accepted_412 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox412) tree412 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox412 midpoint_even_412
  simp only [tree412,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox412,candidate_valid h (FixedTape.midBox ibox412),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox412 101 (FixedTape.rowsAux denominator ibox412 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox412) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_412
private noncomputable def tree411 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree412 tree413
attribute [irreducible] tree411
private theorem accepted_411 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox411) tree411 = true := by
  simp only [tree411,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox411 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox411 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_412 h,accepted_413 h⟩
private noncomputable def tree410 : TapeTree := .split 1 (((81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree411 tree414
attribute [irreducible] tree410
private theorem accepted_410 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox410) tree410 = true := by
  simp only [tree410,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox410 1 (81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) false,decode_split denominator ibox410 1 (81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_411 h,accepted_414 h⟩
private noncomputable def tree409 : TapeTree := .centered (candidateRows ibox409) (candidateRows (FixedTape.midBox ibox409))
attribute [irreducible] tree409
private theorem sign_409 : 2*denominator*(computed denominator (FixedTape.midBox ibox409)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox409).gradient k).lo.natAbs ((computed denominator ibox409).gradient k).hi.natAbs : Int)*((ibox409 k).hi-(ibox409 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox409
    (computed denominator ibox409) (computed denominator (FixedTape.midBox ibox409))
    (by decide +kernel)
private theorem midpoint_even_409 : ∀ k, 2 ∣ (ibox409 k).lo+(ibox409 k).hi := by decide +kernel
private theorem accepted_409 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox409) tree409 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox409 midpoint_even_409
  simp only [tree409,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox409,candidate_valid h (FixedTape.midBox ibox409),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox409 101 (FixedTape.rowsAux denominator ibox409 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox409) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_409
private noncomputable def tree408 : TapeTree := .centered (candidateRows ibox408) (candidateRows (FixedTape.midBox ibox408))
attribute [irreducible] tree408
private theorem sign_408 : 2*denominator*(computed denominator (FixedTape.midBox ibox408)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox408).gradient k).lo.natAbs ((computed denominator ibox408).gradient k).hi.natAbs : Int)*((ibox408 k).hi-(ibox408 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox408
    (computed denominator ibox408) (computed denominator (FixedTape.midBox ibox408))
    (by decide +kernel)
private theorem midpoint_even_408 : ∀ k, 2 ∣ (ibox408 k).lo+(ibox408 k).hi := by decide +kernel
private theorem accepted_408 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox408) tree408 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox408 midpoint_even_408
  simp only [tree408,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox408,candidate_valid h (FixedTape.midBox ibox408),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox408 101 (FixedTape.rowsAux denominator ibox408 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox408) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_408
private noncomputable def tree407 : TapeTree := .split 1 (((81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree408 tree409
attribute [irreducible] tree407
private theorem accepted_407 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox407) tree407 = true := by
  simp only [tree407,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox407 1 (81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) false,decode_split denominator ibox407 1 (81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_408 h,accepted_409 h⟩
private noncomputable def tree406 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree407 tree410
attribute [irreducible] tree406
private theorem accepted_406 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox406) tree406 = true := by
  simp only [tree406,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox406 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox406 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_407 h,accepted_410 h⟩
private noncomputable def tree405 : TapeTree := .centered (candidateRows ibox405) (candidateRows (FixedTape.midBox ibox405))
attribute [irreducible] tree405
private theorem sign_405 : 2*denominator*(computed denominator (FixedTape.midBox ibox405)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox405).gradient k).lo.natAbs ((computed denominator ibox405).gradient k).hi.natAbs : Int)*((ibox405 k).hi-(ibox405 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox405
    (computed denominator ibox405) (computed denominator (FixedTape.midBox ibox405))
    (by decide +kernel)
private theorem midpoint_even_405 : ∀ k, 2 ∣ (ibox405 k).lo+(ibox405 k).hi := by decide +kernel
private theorem accepted_405 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox405) tree405 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox405 midpoint_even_405
  simp only [tree405,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox405,candidate_valid h (FixedTape.midBox ibox405),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox405 101 (FixedTape.rowsAux denominator ibox405 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox405) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_405
private noncomputable def tree404 : TapeTree := .centered (candidateRows ibox404) (candidateRows (FixedTape.midBox ibox404))
attribute [irreducible] tree404
private theorem sign_404 : 2*denominator*(computed denominator (FixedTape.midBox ibox404)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox404).gradient k).lo.natAbs ((computed denominator ibox404).gradient k).hi.natAbs : Int)*((ibox404 k).hi-(ibox404 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox404
    (computed denominator ibox404) (computed denominator (FixedTape.midBox ibox404))
    (by decide +kernel)
private theorem midpoint_even_404 : ∀ k, 2 ∣ (ibox404 k).lo+(ibox404 k).hi := by decide +kernel
private theorem accepted_404 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox404) tree404 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox404 midpoint_even_404
  simp only [tree404,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox404,candidate_valid h (FixedTape.midBox ibox404),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox404 101 (FixedTape.rowsAux denominator ibox404 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox404) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_404
private noncomputable def tree403 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree404 tree405
attribute [irreducible] tree403
private theorem accepted_403 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox403) tree403 = true := by
  simp only [tree403,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox403 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox403 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_404 h,accepted_405 h⟩
private noncomputable def tree402 : TapeTree := .centered (candidateRows ibox402) (candidateRows (FixedTape.midBox ibox402))
attribute [irreducible] tree402
private theorem sign_402 : 2*denominator*(computed denominator (FixedTape.midBox ibox402)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox402).gradient k).lo.natAbs ((computed denominator ibox402).gradient k).hi.natAbs : Int)*((ibox402 k).hi-(ibox402 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox402
    (computed denominator ibox402) (computed denominator (FixedTape.midBox ibox402))
    (by decide +kernel)
private theorem midpoint_even_402 : ∀ k, 2 ∣ (ibox402 k).lo+(ibox402 k).hi := by decide +kernel
private theorem accepted_402 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox402) tree402 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox402 midpoint_even_402
  simp only [tree402,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox402,candidate_valid h (FixedTape.midBox ibox402),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox402 101 (FixedTape.rowsAux denominator ibox402 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox402) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_402
private noncomputable def tree401 : TapeTree := .centered (candidateRows ibox401) (candidateRows (FixedTape.midBox ibox401))
attribute [irreducible] tree401
private theorem sign_401 : 2*denominator*(computed denominator (FixedTape.midBox ibox401)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox401).gradient k).lo.natAbs ((computed denominator ibox401).gradient k).hi.natAbs : Int)*((ibox401 k).hi-(ibox401 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox401
    (computed denominator ibox401) (computed denominator (FixedTape.midBox ibox401))
    (by decide +kernel)
private theorem midpoint_even_401 : ∀ k, 2 ∣ (ibox401 k).lo+(ibox401 k).hi := by decide +kernel
private theorem accepted_401 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox401) tree401 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox401 midpoint_even_401
  simp only [tree401,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox401,candidate_valid h (FixedTape.midBox ibox401),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox401 101 (FixedTape.rowsAux denominator ibox401 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox401) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_401
private noncomputable def tree400 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree401 tree402
attribute [irreducible] tree400
private theorem accepted_400 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox400) tree400 = true := by
  simp only [tree400,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox400 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox400 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_401 h,accepted_402 h⟩
private noncomputable def tree399 : TapeTree := .split 1 (((27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree400 tree403
attribute [irreducible] tree399
private theorem accepted_399 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox399) tree399 = true := by
  simp only [tree399,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox399 1 (27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) false,decode_split denominator ibox399 1 (27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_400 h,accepted_403 h⟩
private noncomputable def tree398 : TapeTree := .centered (candidateRows ibox398) (candidateRows (FixedTape.midBox ibox398))
attribute [irreducible] tree398
private theorem sign_398 : 2*denominator*(computed denominator (FixedTape.midBox ibox398)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox398).gradient k).lo.natAbs ((computed denominator ibox398).gradient k).hi.natAbs : Int)*((ibox398 k).hi-(ibox398 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox398
    (computed denominator ibox398) (computed denominator (FixedTape.midBox ibox398))
    (by decide +kernel)
private theorem midpoint_even_398 : ∀ k, 2 ∣ (ibox398 k).lo+(ibox398 k).hi := by decide +kernel
private theorem accepted_398 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox398) tree398 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox398 midpoint_even_398
  simp only [tree398,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox398,candidate_valid h (FixedTape.midBox ibox398),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox398 101 (FixedTape.rowsAux denominator ibox398 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox398) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_398
private noncomputable def tree397 : TapeTree := .centered (candidateRows ibox397) (candidateRows (FixedTape.midBox ibox397))
attribute [irreducible] tree397
private theorem sign_397 : 2*denominator*(computed denominator (FixedTape.midBox ibox397)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox397).gradient k).lo.natAbs ((computed denominator ibox397).gradient k).hi.natAbs : Int)*((ibox397 k).hi-(ibox397 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox397
    (computed denominator ibox397) (computed denominator (FixedTape.midBox ibox397))
    (by decide +kernel)
private theorem midpoint_even_397 : ∀ k, 2 ∣ (ibox397 k).lo+(ibox397 k).hi := by decide +kernel
private theorem accepted_397 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox397) tree397 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox397 midpoint_even_397
  simp only [tree397,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox397,candidate_valid h (FixedTape.midBox ibox397),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox397 101 (FixedTape.rowsAux denominator ibox397 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox397) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_397
private noncomputable def tree396 : TapeTree := .split 1 (((27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree397 tree398
attribute [irreducible] tree396
private theorem accepted_396 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox396) tree396 = true := by
  simp only [tree396,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox396 1 (27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) false,decode_split denominator ibox396 1 (27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_397 h,accepted_398 h⟩
private noncomputable def tree395 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree396 tree399
attribute [irreducible] tree395
private theorem accepted_395 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox395) tree395 = true := by
  simp only [tree395,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox395 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox395 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_396 h,accepted_399 h⟩
private noncomputable def tree394 : TapeTree := .split 1 (((54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree395 tree406
attribute [irreducible] tree394
private theorem accepted_394 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox394) tree394 = true := by
  simp only [tree394,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox394 1 (54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 : Int) false,decode_split denominator ibox394 1 (54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_395 h,accepted_406 h⟩
private noncomputable def tree393 : TapeTree := .split 1 (((108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree394 tree417
attribute [irreducible] tree393
private theorem accepted_393 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox393) tree393 = true := by
  simp only [tree393,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox393 1 (108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 : Int) false,decode_split denominator ibox393 1 (108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_394 h,accepted_417 h⟩
private noncomputable def tree392 : TapeTree := .split 1 (((216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree393 tree440
attribute [irreducible] tree392
private theorem accepted_392 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox392) tree392 = true := by
  simp only [tree392,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox392 1 (216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 : Int) false,decode_split denominator ibox392 1 (216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_393 h,accepted_440 h⟩
private noncomputable def tree391 : TapeTree := .centered (candidateRows ibox391) (candidateRows (FixedTape.midBox ibox391))
attribute [irreducible] tree391
private theorem sign_391 : 2*denominator*(computed denominator (FixedTape.midBox ibox391)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox391).gradient k).lo.natAbs ((computed denominator ibox391).gradient k).hi.natAbs : Int)*((ibox391 k).hi-(ibox391 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox391
    (computed denominator ibox391) (computed denominator (FixedTape.midBox ibox391))
    (by decide +kernel)
private theorem midpoint_even_391 : ∀ k, 2 ∣ (ibox391 k).lo+(ibox391 k).hi := by decide +kernel
private theorem accepted_391 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox391) tree391 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox391 midpoint_even_391
  simp only [tree391,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox391,candidate_valid h (FixedTape.midBox ibox391),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox391 101 (FixedTape.rowsAux denominator ibox391 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox391) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_391
private noncomputable def tree390 : TapeTree := .centered (candidateRows ibox390) (candidateRows (FixedTape.midBox ibox390))
attribute [irreducible] tree390
private theorem sign_390 : 2*denominator*(computed denominator (FixedTape.midBox ibox390)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox390).gradient k).lo.natAbs ((computed denominator ibox390).gradient k).hi.natAbs : Int)*((ibox390 k).hi-(ibox390 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox390
    (computed denominator ibox390) (computed denominator (FixedTape.midBox ibox390))
    (by decide +kernel)
private theorem midpoint_even_390 : ∀ k, 2 ∣ (ibox390 k).lo+(ibox390 k).hi := by decide +kernel
private theorem accepted_390 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox390) tree390 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox390 midpoint_even_390
  simp only [tree390,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox390,candidate_valid h (FixedTape.midBox ibox390),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox390 101 (FixedTape.rowsAux denominator ibox390 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox390) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_390
private noncomputable def tree389 : TapeTree := .split 1 (((405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree390 tree391
attribute [irreducible] tree389
private theorem accepted_389 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox389) tree389 = true := by
  simp only [tree389,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox389 1 (405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) false,decode_split denominator ibox389 1 (405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_390 h,accepted_391 h⟩
private noncomputable def tree388 : TapeTree := .centered (candidateRows ibox388) (candidateRows (FixedTape.midBox ibox388))
attribute [irreducible] tree388
private theorem sign_388 : 2*denominator*(computed denominator (FixedTape.midBox ibox388)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox388).gradient k).lo.natAbs ((computed denominator ibox388).gradient k).hi.natAbs : Int)*((ibox388 k).hi-(ibox388 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox388
    (computed denominator ibox388) (computed denominator (FixedTape.midBox ibox388))
    (by decide +kernel)
private theorem midpoint_even_388 : ∀ k, 2 ∣ (ibox388 k).lo+(ibox388 k).hi := by decide +kernel
private theorem accepted_388 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox388) tree388 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox388 midpoint_even_388
  simp only [tree388,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox388,candidate_valid h (FixedTape.midBox ibox388),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox388 101 (FixedTape.rowsAux denominator ibox388 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox388) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_388
private noncomputable def tree387 : TapeTree := .centered (candidateRows ibox387) (candidateRows (FixedTape.midBox ibox387))
attribute [irreducible] tree387
private theorem sign_387 : 2*denominator*(computed denominator (FixedTape.midBox ibox387)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox387).gradient k).lo.natAbs ((computed denominator ibox387).gradient k).hi.natAbs : Int)*((ibox387 k).hi-(ibox387 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox387
    (computed denominator ibox387) (computed denominator (FixedTape.midBox ibox387))
    (by decide +kernel)
private theorem midpoint_even_387 : ∀ k, 2 ∣ (ibox387 k).lo+(ibox387 k).hi := by decide +kernel
private theorem accepted_387 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox387) tree387 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox387 midpoint_even_387
  simp only [tree387,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox387,candidate_valid h (FixedTape.midBox ibox387),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox387 101 (FixedTape.rowsAux denominator ibox387 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox387) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_387
private noncomputable def tree386 : TapeTree := .split 1 (((405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree387 tree388
attribute [irreducible] tree386
private theorem accepted_386 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox386) tree386 = true := by
  simp only [tree386,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox386 1 (405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) false,decode_split denominator ibox386 1 (405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_387 h,accepted_388 h⟩
private noncomputable def tree385 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree386 tree389
attribute [irreducible] tree385
private theorem accepted_385 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox385) tree385 = true := by
  simp only [tree385,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox385 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox385 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_386 h,accepted_389 h⟩
private noncomputable def tree384 : TapeTree := .centered (candidateRows ibox384) (candidateRows (FixedTape.midBox ibox384))
attribute [irreducible] tree384
private theorem sign_384 : 2*denominator*(computed denominator (FixedTape.midBox ibox384)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox384).gradient k).lo.natAbs ((computed denominator ibox384).gradient k).hi.natAbs : Int)*((ibox384 k).hi-(ibox384 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox384
    (computed denominator ibox384) (computed denominator (FixedTape.midBox ibox384))
    (by decide +kernel)
private theorem midpoint_even_384 : ∀ k, 2 ∣ (ibox384 k).lo+(ibox384 k).hi := by decide +kernel
private theorem accepted_384 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox384) tree384 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox384 midpoint_even_384
  simp only [tree384,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox384,candidate_valid h (FixedTape.midBox ibox384),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox384 101 (FixedTape.rowsAux denominator ibox384 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox384) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_384
private noncomputable def tree383 : TapeTree := .centered (candidateRows ibox383) (candidateRows (FixedTape.midBox ibox383))
attribute [irreducible] tree383
private theorem sign_383 : 2*denominator*(computed denominator (FixedTape.midBox ibox383)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox383).gradient k).lo.natAbs ((computed denominator ibox383).gradient k).hi.natAbs : Int)*((ibox383 k).hi-(ibox383 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox383
    (computed denominator ibox383) (computed denominator (FixedTape.midBox ibox383))
    (by decide +kernel)
private theorem midpoint_even_383 : ∀ k, 2 ∣ (ibox383 k).lo+(ibox383 k).hi := by decide +kernel
private theorem accepted_383 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox383) tree383 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox383 midpoint_even_383
  simp only [tree383,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox383,candidate_valid h (FixedTape.midBox ibox383),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox383 101 (FixedTape.rowsAux denominator ibox383 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox383) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_383
private noncomputable def tree382 : TapeTree := .split 1 (((351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree383 tree384
attribute [irreducible] tree382
private theorem accepted_382 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox382) tree382 = true := by
  simp only [tree382,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox382 1 (351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) false,decode_split denominator ibox382 1 (351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_383 h,accepted_384 h⟩
private noncomputable def tree381 : TapeTree := .centered (candidateRows ibox381) (candidateRows (FixedTape.midBox ibox381))
attribute [irreducible] tree381
private theorem sign_381 : 2*denominator*(computed denominator (FixedTape.midBox ibox381)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox381).gradient k).lo.natAbs ((computed denominator ibox381).gradient k).hi.natAbs : Int)*((ibox381 k).hi-(ibox381 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox381
    (computed denominator ibox381) (computed denominator (FixedTape.midBox ibox381))
    (by decide +kernel)
private theorem midpoint_even_381 : ∀ k, 2 ∣ (ibox381 k).lo+(ibox381 k).hi := by decide +kernel
private theorem accepted_381 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox381) tree381 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox381 midpoint_even_381
  simp only [tree381,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox381,candidate_valid h (FixedTape.midBox ibox381),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox381 101 (FixedTape.rowsAux denominator ibox381 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox381) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_381
private noncomputable def tree380 : TapeTree := .centered (candidateRows ibox380) (candidateRows (FixedTape.midBox ibox380))
attribute [irreducible] tree380
private theorem sign_380 : 2*denominator*(computed denominator (FixedTape.midBox ibox380)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox380).gradient k).lo.natAbs ((computed denominator ibox380).gradient k).hi.natAbs : Int)*((ibox380 k).hi-(ibox380 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox380
    (computed denominator ibox380) (computed denominator (FixedTape.midBox ibox380))
    (by decide +kernel)
private theorem midpoint_even_380 : ∀ k, 2 ∣ (ibox380 k).lo+(ibox380 k).hi := by decide +kernel
private theorem accepted_380 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox380) tree380 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox380 midpoint_even_380
  simp only [tree380,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox380,candidate_valid h (FixedTape.midBox ibox380),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox380 101 (FixedTape.rowsAux denominator ibox380 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox380) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_380
private noncomputable def tree379 : TapeTree := .split 1 (((351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree380 tree381
attribute [irreducible] tree379
private theorem accepted_379 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox379) tree379 = true := by
  simp only [tree379,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox379 1 (351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) false,decode_split denominator ibox379 1 (351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_380 h,accepted_381 h⟩
private noncomputable def tree378 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree379 tree382
attribute [irreducible] tree378
private theorem accepted_378 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox378) tree378 = true := by
  simp only [tree378,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox378 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox378 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_379 h,accepted_382 h⟩
private noncomputable def tree377 : TapeTree := .split 1 (((378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree378 tree385
attribute [irreducible] tree377
private theorem accepted_377 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox377) tree377 = true := by
  simp only [tree377,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox377 1 (378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 : Int) false,decode_split denominator ibox377 1 (378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_378 h,accepted_385 h⟩
private noncomputable def tree376 : TapeTree := .centered (candidateRows ibox376) (candidateRows (FixedTape.midBox ibox376))
attribute [irreducible] tree376
private theorem sign_376 : 2*denominator*(computed denominator (FixedTape.midBox ibox376)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox376).gradient k).lo.natAbs ((computed denominator ibox376).gradient k).hi.natAbs : Int)*((ibox376 k).hi-(ibox376 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox376
    (computed denominator ibox376) (computed denominator (FixedTape.midBox ibox376))
    (by decide +kernel)
private theorem midpoint_even_376 : ∀ k, 2 ∣ (ibox376 k).lo+(ibox376 k).hi := by decide +kernel
private theorem accepted_376 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox376) tree376 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox376 midpoint_even_376
  simp only [tree376,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox376,candidate_valid h (FixedTape.midBox ibox376),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox376 101 (FixedTape.rowsAux denominator ibox376 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox376) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_376
private noncomputable def tree375 : TapeTree := .centered (candidateRows ibox375) (candidateRows (FixedTape.midBox ibox375))
attribute [irreducible] tree375
private theorem sign_375 : 2*denominator*(computed denominator (FixedTape.midBox ibox375)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox375).gradient k).lo.natAbs ((computed denominator ibox375).gradient k).hi.natAbs : Int)*((ibox375 k).hi-(ibox375 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox375
    (computed denominator ibox375) (computed denominator (FixedTape.midBox ibox375))
    (by decide +kernel)
private theorem midpoint_even_375 : ∀ k, 2 ∣ (ibox375 k).lo+(ibox375 k).hi := by decide +kernel
private theorem accepted_375 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox375) tree375 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox375 midpoint_even_375
  simp only [tree375,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox375,candidate_valid h (FixedTape.midBox ibox375),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox375 101 (FixedTape.rowsAux denominator ibox375 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox375) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_375
private noncomputable def tree374 : TapeTree := .split 1 (((297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree375 tree376
attribute [irreducible] tree374
private theorem accepted_374 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox374) tree374 = true := by
  simp only [tree374,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox374 1 (297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) false,decode_split denominator ibox374 1 (297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_375 h,accepted_376 h⟩
private noncomputable def tree373 : TapeTree := .centered (candidateRows ibox373) (candidateRows (FixedTape.midBox ibox373))
attribute [irreducible] tree373
private theorem sign_373 : 2*denominator*(computed denominator (FixedTape.midBox ibox373)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox373).gradient k).lo.natAbs ((computed denominator ibox373).gradient k).hi.natAbs : Int)*((ibox373 k).hi-(ibox373 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox373
    (computed denominator ibox373) (computed denominator (FixedTape.midBox ibox373))
    (by decide +kernel)
private theorem midpoint_even_373 : ∀ k, 2 ∣ (ibox373 k).lo+(ibox373 k).hi := by decide +kernel
private theorem accepted_373 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox373) tree373 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox373 midpoint_even_373
  simp only [tree373,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox373,candidate_valid h (FixedTape.midBox ibox373),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox373 101 (FixedTape.rowsAux denominator ibox373 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox373) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_373
private noncomputable def tree372 : TapeTree := .centered (candidateRows ibox372) (candidateRows (FixedTape.midBox ibox372))
attribute [irreducible] tree372
private theorem sign_372 : 2*denominator*(computed denominator (FixedTape.midBox ibox372)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox372).gradient k).lo.natAbs ((computed denominator ibox372).gradient k).hi.natAbs : Int)*((ibox372 k).hi-(ibox372 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox372
    (computed denominator ibox372) (computed denominator (FixedTape.midBox ibox372))
    (by decide +kernel)
private theorem midpoint_even_372 : ∀ k, 2 ∣ (ibox372 k).lo+(ibox372 k).hi := by decide +kernel
private theorem accepted_372 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox372) tree372 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox372 midpoint_even_372
  simp only [tree372,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox372,candidate_valid h (FixedTape.midBox ibox372),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox372 101 (FixedTape.rowsAux denominator ibox372 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox372) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_372
private noncomputable def tree371 : TapeTree := .split 1 (((297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree372 tree373
attribute [irreducible] tree371
private theorem accepted_371 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox371) tree371 = true := by
  simp only [tree371,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox371 1 (297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) false,decode_split denominator ibox371 1 (297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_372 h,accepted_373 h⟩
private noncomputable def tree370 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree371 tree374
attribute [irreducible] tree370
private theorem accepted_370 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox370) tree370 = true := by
  simp only [tree370,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox370 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox370 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_371 h,accepted_374 h⟩
private noncomputable def tree369 : TapeTree := .centered (candidateRows ibox369) (candidateRows (FixedTape.midBox ibox369))
attribute [irreducible] tree369
private theorem sign_369 : 2*denominator*(computed denominator (FixedTape.midBox ibox369)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox369).gradient k).lo.natAbs ((computed denominator ibox369).gradient k).hi.natAbs : Int)*((ibox369 k).hi-(ibox369 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox369
    (computed denominator ibox369) (computed denominator (FixedTape.midBox ibox369))
    (by decide +kernel)
private theorem midpoint_even_369 : ∀ k, 2 ∣ (ibox369 k).lo+(ibox369 k).hi := by decide +kernel
private theorem accepted_369 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox369) tree369 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox369 midpoint_even_369
  simp only [tree369,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox369,candidate_valid h (FixedTape.midBox ibox369),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox369 101 (FixedTape.rowsAux denominator ibox369 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox369) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_369
private noncomputable def tree368 : TapeTree := .centered (candidateRows ibox368) (candidateRows (FixedTape.midBox ibox368))
attribute [irreducible] tree368
private theorem sign_368 : 2*denominator*(computed denominator (FixedTape.midBox ibox368)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox368).gradient k).lo.natAbs ((computed denominator ibox368).gradient k).hi.natAbs : Int)*((ibox368 k).hi-(ibox368 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox368
    (computed denominator ibox368) (computed denominator (FixedTape.midBox ibox368))
    (by decide +kernel)
private theorem midpoint_even_368 : ∀ k, 2 ∣ (ibox368 k).lo+(ibox368 k).hi := by decide +kernel
private theorem accepted_368 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox368) tree368 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox368 midpoint_even_368
  simp only [tree368,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox368,candidate_valid h (FixedTape.midBox ibox368),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox368 101 (FixedTape.rowsAux denominator ibox368 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox368) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_368
private noncomputable def tree367 : TapeTree := .split 1 (((243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree368 tree369
attribute [irreducible] tree367
private theorem accepted_367 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox367) tree367 = true := by
  simp only [tree367,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox367 1 (243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) false,decode_split denominator ibox367 1 (243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_368 h,accepted_369 h⟩
private noncomputable def tree366 : TapeTree := .centered (candidateRows ibox366) (candidateRows (FixedTape.midBox ibox366))
attribute [irreducible] tree366
private theorem sign_366 : 2*denominator*(computed denominator (FixedTape.midBox ibox366)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox366).gradient k).lo.natAbs ((computed denominator ibox366).gradient k).hi.natAbs : Int)*((ibox366 k).hi-(ibox366 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox366
    (computed denominator ibox366) (computed denominator (FixedTape.midBox ibox366))
    (by decide +kernel)
private theorem midpoint_even_366 : ∀ k, 2 ∣ (ibox366 k).lo+(ibox366 k).hi := by decide +kernel
private theorem accepted_366 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox366) tree366 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox366 midpoint_even_366
  simp only [tree366,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox366,candidate_valid h (FixedTape.midBox ibox366),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox366 101 (FixedTape.rowsAux denominator ibox366 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox366) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_366
private noncomputable def tree365 : TapeTree := .centered (candidateRows ibox365) (candidateRows (FixedTape.midBox ibox365))
attribute [irreducible] tree365
private theorem sign_365 : 2*denominator*(computed denominator (FixedTape.midBox ibox365)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox365).gradient k).lo.natAbs ((computed denominator ibox365).gradient k).hi.natAbs : Int)*((ibox365 k).hi-(ibox365 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox365
    (computed denominator ibox365) (computed denominator (FixedTape.midBox ibox365))
    (by decide +kernel)
private theorem midpoint_even_365 : ∀ k, 2 ∣ (ibox365 k).lo+(ibox365 k).hi := by decide +kernel
private theorem accepted_365 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox365) tree365 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox365 midpoint_even_365
  simp only [tree365,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox365,candidate_valid h (FixedTape.midBox ibox365),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox365 101 (FixedTape.rowsAux denominator ibox365 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox365) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_365
private noncomputable def tree364 : TapeTree := .split 1 (((243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree365 tree366
attribute [irreducible] tree364
private theorem accepted_364 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox364) tree364 = true := by
  simp only [tree364,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox364 1 (243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) false,decode_split denominator ibox364 1 (243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_365 h,accepted_366 h⟩
private noncomputable def tree363 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree364 tree367
attribute [irreducible] tree363
private theorem accepted_363 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox363) tree363 = true := by
  simp only [tree363,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox363 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox363 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_364 h,accepted_367 h⟩
private noncomputable def tree362 : TapeTree := .split 1 (((270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree363 tree370
attribute [irreducible] tree362
private theorem accepted_362 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox362) tree362 = true := by
  simp only [tree362,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox362 1 (270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 : Int) false,decode_split denominator ibox362 1 (270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_363 h,accepted_370 h⟩
private noncomputable def tree361 : TapeTree := .split 1 (((324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree362 tree377
attribute [irreducible] tree361
private theorem accepted_361 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox361) tree361 = true := by
  simp only [tree361,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox361 1 (324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 : Int) false,decode_split denominator ibox361 1 (324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_362 h,accepted_377 h⟩
private noncomputable def tree360 : TapeTree := .centered (candidateRows ibox360) (candidateRows (FixedTape.midBox ibox360))
attribute [irreducible] tree360
private theorem sign_360 : 2*denominator*(computed denominator (FixedTape.midBox ibox360)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox360).gradient k).lo.natAbs ((computed denominator ibox360).gradient k).hi.natAbs : Int)*((ibox360 k).hi-(ibox360 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox360
    (computed denominator ibox360) (computed denominator (FixedTape.midBox ibox360))
    (by decide +kernel)
private theorem midpoint_even_360 : ∀ k, 2 ∣ (ibox360 k).lo+(ibox360 k).hi := by decide +kernel
private theorem accepted_360 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox360) tree360 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox360 midpoint_even_360
  simp only [tree360,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox360,candidate_valid h (FixedTape.midBox ibox360),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox360 101 (FixedTape.rowsAux denominator ibox360 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox360) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_360
private noncomputable def tree359 : TapeTree := .centered (candidateRows ibox359) (candidateRows (FixedTape.midBox ibox359))
attribute [irreducible] tree359
private theorem sign_359 : 2*denominator*(computed denominator (FixedTape.midBox ibox359)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox359).gradient k).lo.natAbs ((computed denominator ibox359).gradient k).hi.natAbs : Int)*((ibox359 k).hi-(ibox359 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox359
    (computed denominator ibox359) (computed denominator (FixedTape.midBox ibox359))
    (by decide +kernel)
private theorem midpoint_even_359 : ∀ k, 2 ∣ (ibox359 k).lo+(ibox359 k).hi := by decide +kernel
private theorem accepted_359 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox359) tree359 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox359 midpoint_even_359
  simp only [tree359,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox359,candidate_valid h (FixedTape.midBox ibox359),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox359 101 (FixedTape.rowsAux denominator ibox359 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox359) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_359
private noncomputable def tree358 : TapeTree := .split 1 (((189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree359 tree360
attribute [irreducible] tree358
private theorem accepted_358 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox358) tree358 = true := by
  simp only [tree358,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox358 1 (189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) false,decode_split denominator ibox358 1 (189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_359 h,accepted_360 h⟩
private noncomputable def tree357 : TapeTree := .centered (candidateRows ibox357) (candidateRows (FixedTape.midBox ibox357))
attribute [irreducible] tree357
private theorem sign_357 : 2*denominator*(computed denominator (FixedTape.midBox ibox357)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox357).gradient k).lo.natAbs ((computed denominator ibox357).gradient k).hi.natAbs : Int)*((ibox357 k).hi-(ibox357 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox357
    (computed denominator ibox357) (computed denominator (FixedTape.midBox ibox357))
    (by decide +kernel)
private theorem midpoint_even_357 : ∀ k, 2 ∣ (ibox357 k).lo+(ibox357 k).hi := by decide +kernel
private theorem accepted_357 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox357) tree357 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox357 midpoint_even_357
  simp only [tree357,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox357,candidate_valid h (FixedTape.midBox ibox357),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox357 101 (FixedTape.rowsAux denominator ibox357 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox357) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_357
private noncomputable def tree356 : TapeTree := .centered (candidateRows ibox356) (candidateRows (FixedTape.midBox ibox356))
attribute [irreducible] tree356
private theorem sign_356 : 2*denominator*(computed denominator (FixedTape.midBox ibox356)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox356).gradient k).lo.natAbs ((computed denominator ibox356).gradient k).hi.natAbs : Int)*((ibox356 k).hi-(ibox356 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox356
    (computed denominator ibox356) (computed denominator (FixedTape.midBox ibox356))
    (by decide +kernel)
private theorem midpoint_even_356 : ∀ k, 2 ∣ (ibox356 k).lo+(ibox356 k).hi := by decide +kernel
private theorem accepted_356 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox356) tree356 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox356 midpoint_even_356
  simp only [tree356,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox356,candidate_valid h (FixedTape.midBox ibox356),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox356 101 (FixedTape.rowsAux denominator ibox356 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox356) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_356
private noncomputable def tree355 : TapeTree := .split 1 (((189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree356 tree357
attribute [irreducible] tree355
private theorem accepted_355 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox355) tree355 = true := by
  simp only [tree355,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox355 1 (189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) false,decode_split denominator ibox355 1 (189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_356 h,accepted_357 h⟩
private noncomputable def tree354 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree355 tree358
attribute [irreducible] tree354
private theorem accepted_354 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox354) tree354 = true := by
  simp only [tree354,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox354 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox354 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_355 h,accepted_358 h⟩
private noncomputable def tree353 : TapeTree := .centered (candidateRows ibox353) (candidateRows (FixedTape.midBox ibox353))
attribute [irreducible] tree353
private theorem sign_353 : 2*denominator*(computed denominator (FixedTape.midBox ibox353)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox353).gradient k).lo.natAbs ((computed denominator ibox353).gradient k).hi.natAbs : Int)*((ibox353 k).hi-(ibox353 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox353
    (computed denominator ibox353) (computed denominator (FixedTape.midBox ibox353))
    (by decide +kernel)
private theorem midpoint_even_353 : ∀ k, 2 ∣ (ibox353 k).lo+(ibox353 k).hi := by decide +kernel
private theorem accepted_353 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox353) tree353 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox353 midpoint_even_353
  simp only [tree353,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox353,candidate_valid h (FixedTape.midBox ibox353),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox353 101 (FixedTape.rowsAux denominator ibox353 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox353) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_353
private noncomputable def tree352 : TapeTree := .centered (candidateRows ibox352) (candidateRows (FixedTape.midBox ibox352))
attribute [irreducible] tree352
private theorem sign_352 : 2*denominator*(computed denominator (FixedTape.midBox ibox352)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox352).gradient k).lo.natAbs ((computed denominator ibox352).gradient k).hi.natAbs : Int)*((ibox352 k).hi-(ibox352 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox352
    (computed denominator ibox352) (computed denominator (FixedTape.midBox ibox352))
    (by decide +kernel)
private theorem midpoint_even_352 : ∀ k, 2 ∣ (ibox352 k).lo+(ibox352 k).hi := by decide +kernel
private theorem accepted_352 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox352) tree352 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox352 midpoint_even_352
  simp only [tree352,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox352,candidate_valid h (FixedTape.midBox ibox352),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox352 101 (FixedTape.rowsAux denominator ibox352 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox352) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_352
private noncomputable def tree351 : TapeTree := .split 1 (((135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree352 tree353
attribute [irreducible] tree351
private theorem accepted_351 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox351) tree351 = true := by
  simp only [tree351,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox351 1 (135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) false,decode_split denominator ibox351 1 (135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_352 h,accepted_353 h⟩
private noncomputable def tree350 : TapeTree := .centered (candidateRows ibox350) (candidateRows (FixedTape.midBox ibox350))
attribute [irreducible] tree350
private theorem sign_350 : 2*denominator*(computed denominator (FixedTape.midBox ibox350)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox350).gradient k).lo.natAbs ((computed denominator ibox350).gradient k).hi.natAbs : Int)*((ibox350 k).hi-(ibox350 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox350
    (computed denominator ibox350) (computed denominator (FixedTape.midBox ibox350))
    (by decide +kernel)
private theorem midpoint_even_350 : ∀ k, 2 ∣ (ibox350 k).lo+(ibox350 k).hi := by decide +kernel
private theorem accepted_350 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox350) tree350 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox350 midpoint_even_350
  simp only [tree350,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox350,candidate_valid h (FixedTape.midBox ibox350),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox350 101 (FixedTape.rowsAux denominator ibox350 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox350) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_350
private noncomputable def tree349 : TapeTree := .centered (candidateRows ibox349) (candidateRows (FixedTape.midBox ibox349))
attribute [irreducible] tree349
private theorem sign_349 : 2*denominator*(computed denominator (FixedTape.midBox ibox349)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox349).gradient k).lo.natAbs ((computed denominator ibox349).gradient k).hi.natAbs : Int)*((ibox349 k).hi-(ibox349 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox349
    (computed denominator ibox349) (computed denominator (FixedTape.midBox ibox349))
    (by decide +kernel)
private theorem midpoint_even_349 : ∀ k, 2 ∣ (ibox349 k).lo+(ibox349 k).hi := by decide +kernel
private theorem accepted_349 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox349) tree349 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox349 midpoint_even_349
  simp only [tree349,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox349,candidate_valid h (FixedTape.midBox ibox349),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox349 101 (FixedTape.rowsAux denominator ibox349 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox349) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_349
private noncomputable def tree348 : TapeTree := .split 1 (((135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree349 tree350
attribute [irreducible] tree348
private theorem accepted_348 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox348) tree348 = true := by
  simp only [tree348,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox348 1 (135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) false,decode_split denominator ibox348 1 (135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_349 h,accepted_350 h⟩
private noncomputable def tree347 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree348 tree351
attribute [irreducible] tree347
private theorem accepted_347 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox347) tree347 = true := by
  simp only [tree347,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox347 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox347 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_348 h,accepted_351 h⟩
private noncomputable def tree346 : TapeTree := .split 1 (((162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree347 tree354
attribute [irreducible] tree346
private theorem accepted_346 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox346) tree346 = true := by
  simp only [tree346,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox346 1 (162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 : Int) false,decode_split denominator ibox346 1 (162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_347 h,accepted_354 h⟩
private noncomputable def tree345 : TapeTree := .centered (candidateRows ibox345) (candidateRows (FixedTape.midBox ibox345))
attribute [irreducible] tree345
private theorem sign_345 : 2*denominator*(computed denominator (FixedTape.midBox ibox345)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox345).gradient k).lo.natAbs ((computed denominator ibox345).gradient k).hi.natAbs : Int)*((ibox345 k).hi-(ibox345 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox345
    (computed denominator ibox345) (computed denominator (FixedTape.midBox ibox345))
    (by decide +kernel)
private theorem midpoint_even_345 : ∀ k, 2 ∣ (ibox345 k).lo+(ibox345 k).hi := by decide +kernel
private theorem accepted_345 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox345) tree345 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox345 midpoint_even_345
  simp only [tree345,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox345,candidate_valid h (FixedTape.midBox ibox345),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox345 101 (FixedTape.rowsAux denominator ibox345 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox345) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_345
private noncomputable def tree344 : TapeTree := .centered (candidateRows ibox344) (candidateRows (FixedTape.midBox ibox344))
attribute [irreducible] tree344
private theorem sign_344 : 2*denominator*(computed denominator (FixedTape.midBox ibox344)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox344).gradient k).lo.natAbs ((computed denominator ibox344).gradient k).hi.natAbs : Int)*((ibox344 k).hi-(ibox344 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox344
    (computed denominator ibox344) (computed denominator (FixedTape.midBox ibox344))
    (by decide +kernel)
private theorem midpoint_even_344 : ∀ k, 2 ∣ (ibox344 k).lo+(ibox344 k).hi := by decide +kernel
private theorem accepted_344 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox344) tree344 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox344 midpoint_even_344
  simp only [tree344,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox344,candidate_valid h (FixedTape.midBox ibox344),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox344 101 (FixedTape.rowsAux denominator ibox344 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox344) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_344
private noncomputable def tree343 : TapeTree := .split 1 (((81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree344 tree345
attribute [irreducible] tree343
private theorem accepted_343 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox343) tree343 = true := by
  simp only [tree343,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox343 1 (81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) false,decode_split denominator ibox343 1 (81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_344 h,accepted_345 h⟩
private noncomputable def tree342 : TapeTree := .centered (candidateRows ibox342) (candidateRows (FixedTape.midBox ibox342))
attribute [irreducible] tree342
private theorem sign_342 : 2*denominator*(computed denominator (FixedTape.midBox ibox342)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox342).gradient k).lo.natAbs ((computed denominator ibox342).gradient k).hi.natAbs : Int)*((ibox342 k).hi-(ibox342 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox342
    (computed denominator ibox342) (computed denominator (FixedTape.midBox ibox342))
    (by decide +kernel)
private theorem midpoint_even_342 : ∀ k, 2 ∣ (ibox342 k).lo+(ibox342 k).hi := by decide +kernel
private theorem accepted_342 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox342) tree342 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox342 midpoint_even_342
  simp only [tree342,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox342,candidate_valid h (FixedTape.midBox ibox342),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox342 101 (FixedTape.rowsAux denominator ibox342 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox342) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_342
private noncomputable def tree341 : TapeTree := .centered (candidateRows ibox341) (candidateRows (FixedTape.midBox ibox341))
attribute [irreducible] tree341
private theorem sign_341 : 2*denominator*(computed denominator (FixedTape.midBox ibox341)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox341).gradient k).lo.natAbs ((computed denominator ibox341).gradient k).hi.natAbs : Int)*((ibox341 k).hi-(ibox341 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox341
    (computed denominator ibox341) (computed denominator (FixedTape.midBox ibox341))
    (by decide +kernel)
private theorem midpoint_even_341 : ∀ k, 2 ∣ (ibox341 k).lo+(ibox341 k).hi := by decide +kernel
private theorem accepted_341 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox341) tree341 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox341 midpoint_even_341
  simp only [tree341,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox341,candidate_valid h (FixedTape.midBox ibox341),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox341 101 (FixedTape.rowsAux denominator ibox341 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox341) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_341
private noncomputable def tree340 : TapeTree := .split 1 (((81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree341 tree342
attribute [irreducible] tree340
private theorem accepted_340 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox340) tree340 = true := by
  simp only [tree340,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox340 1 (81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) false,decode_split denominator ibox340 1 (81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_341 h,accepted_342 h⟩
private noncomputable def tree339 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree340 tree343
attribute [irreducible] tree339
private theorem accepted_339 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox339) tree339 = true := by
  simp only [tree339,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox339 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox339 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_340 h,accepted_343 h⟩
private noncomputable def tree338 : TapeTree := .centered (candidateRows ibox338) (candidateRows (FixedTape.midBox ibox338))
attribute [irreducible] tree338
private theorem sign_338 : 2*denominator*(computed denominator (FixedTape.midBox ibox338)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox338).gradient k).lo.natAbs ((computed denominator ibox338).gradient k).hi.natAbs : Int)*((ibox338 k).hi-(ibox338 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox338
    (computed denominator ibox338) (computed denominator (FixedTape.midBox ibox338))
    (by decide +kernel)
private theorem midpoint_even_338 : ∀ k, 2 ∣ (ibox338 k).lo+(ibox338 k).hi := by decide +kernel
private theorem accepted_338 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox338) tree338 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox338 midpoint_even_338
  simp only [tree338,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox338,candidate_valid h (FixedTape.midBox ibox338),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox338 101 (FixedTape.rowsAux denominator ibox338 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox338) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_338
private noncomputable def tree337 : TapeTree := .centered (candidateRows ibox337) (candidateRows (FixedTape.midBox ibox337))
attribute [irreducible] tree337
private theorem sign_337 : 2*denominator*(computed denominator (FixedTape.midBox ibox337)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox337).gradient k).lo.natAbs ((computed denominator ibox337).gradient k).hi.natAbs : Int)*((ibox337 k).hi-(ibox337 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox337
    (computed denominator ibox337) (computed denominator (FixedTape.midBox ibox337))
    (by decide +kernel)
private theorem midpoint_even_337 : ∀ k, 2 ∣ (ibox337 k).lo+(ibox337 k).hi := by decide +kernel
private theorem accepted_337 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox337) tree337 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox337 midpoint_even_337
  simp only [tree337,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox337,candidate_valid h (FixedTape.midBox ibox337),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox337 101 (FixedTape.rowsAux denominator ibox337 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox337) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_337
private noncomputable def tree336 : TapeTree := .split 1 (((27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree337 tree338
attribute [irreducible] tree336
private theorem accepted_336 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox336) tree336 = true := by
  simp only [tree336,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox336 1 (27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) false,decode_split denominator ibox336 1 (27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_337 h,accepted_338 h⟩
private noncomputable def tree335 : TapeTree := .centered (candidateRows ibox335) (candidateRows (FixedTape.midBox ibox335))
attribute [irreducible] tree335
private theorem sign_335 : 2*denominator*(computed denominator (FixedTape.midBox ibox335)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox335).gradient k).lo.natAbs ((computed denominator ibox335).gradient k).hi.natAbs : Int)*((ibox335 k).hi-(ibox335 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox335
    (computed denominator ibox335) (computed denominator (FixedTape.midBox ibox335))
    (by decide +kernel)
private theorem midpoint_even_335 : ∀ k, 2 ∣ (ibox335 k).lo+(ibox335 k).hi := by decide +kernel
private theorem accepted_335 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox335) tree335 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox335 midpoint_even_335
  simp only [tree335,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox335,candidate_valid h (FixedTape.midBox ibox335),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox335 101 (FixedTape.rowsAux denominator ibox335 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox335) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_335
private noncomputable def tree334 : TapeTree := .centered (candidateRows ibox334) (candidateRows (FixedTape.midBox ibox334))
attribute [irreducible] tree334
private theorem sign_334 : 2*denominator*(computed denominator (FixedTape.midBox ibox334)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox334).gradient k).lo.natAbs ((computed denominator ibox334).gradient k).hi.natAbs : Int)*((ibox334 k).hi-(ibox334 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox334
    (computed denominator ibox334) (computed denominator (FixedTape.midBox ibox334))
    (by decide +kernel)
private theorem midpoint_even_334 : ∀ k, 2 ∣ (ibox334 k).lo+(ibox334 k).hi := by decide +kernel
private theorem accepted_334 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox334) tree334 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox334 midpoint_even_334
  simp only [tree334,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox334,candidate_valid h (FixedTape.midBox ibox334),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox334 101 (FixedTape.rowsAux denominator ibox334 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox334) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_334
private noncomputable def tree333 : TapeTree := .split 1 (((27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree334 tree335
attribute [irreducible] tree333
private theorem accepted_333 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox333) tree333 = true := by
  simp only [tree333,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox333 1 (27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) false,decode_split denominator ibox333 1 (27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_334 h,accepted_335 h⟩
private noncomputable def tree332 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree333 tree336
attribute [irreducible] tree332
private theorem accepted_332 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox332) tree332 = true := by
  simp only [tree332,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox332 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox332 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_333 h,accepted_336 h⟩
private noncomputable def tree331 : TapeTree := .split 1 (((54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree332 tree339
attribute [irreducible] tree331
private theorem accepted_331 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox331) tree331 = true := by
  simp only [tree331,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox331 1 (54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 : Int) false,decode_split denominator ibox331 1 (54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_332 h,accepted_339 h⟩
private noncomputable def tree330 : TapeTree := .split 1 (((108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree331 tree346
attribute [irreducible] tree330
private theorem accepted_330 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox330) tree330 = true := by
  simp only [tree330,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox330 1 (108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 : Int) false,decode_split denominator ibox330 1 (108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_331 h,accepted_346 h⟩
private noncomputable def tree329 : TapeTree := .split 1 (((216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree330 tree361
attribute [irreducible] tree329
private theorem accepted_329 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox329) tree329 = true := by
  simp only [tree329,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox329 1 (216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 : Int) false,decode_split denominator ibox329 1 (216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_330 h,accepted_361 h⟩
private noncomputable def tree328 : TapeTree := .split 2 (((811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree329 tree392
attribute [irreducible] tree328
private theorem accepted_328 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox328) tree328 = true := by
  simp only [tree328,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox328 2 (811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 : Int) false,decode_split denominator ibox328 2 (811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_329 h,accepted_392 h⟩
private noncomputable def tree327 : TapeTree := .centered (candidateRows ibox327) (candidateRows (FixedTape.midBox ibox327))
attribute [irreducible] tree327
private theorem sign_327 : 2*denominator*(computed denominator (FixedTape.midBox ibox327)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox327).gradient k).lo.natAbs ((computed denominator ibox327).gradient k).hi.natAbs : Int)*((ibox327 k).hi-(ibox327 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox327
    (computed denominator ibox327) (computed denominator (FixedTape.midBox ibox327))
    (by decide +kernel)
private theorem midpoint_even_327 : ∀ k, 2 ∣ (ibox327 k).lo+(ibox327 k).hi := by decide +kernel
private theorem accepted_327 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox327) tree327 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox327 midpoint_even_327
  simp only [tree327,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox327,candidate_valid h (FixedTape.midBox ibox327),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox327 101 (FixedTape.rowsAux denominator ibox327 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox327) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_327
private noncomputable def tree326 : TapeTree := .centered (candidateRows ibox326) (candidateRows (FixedTape.midBox ibox326))
attribute [irreducible] tree326
private theorem sign_326 : 2*denominator*(computed denominator (FixedTape.midBox ibox326)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox326).gradient k).lo.natAbs ((computed denominator ibox326).gradient k).hi.natAbs : Int)*((ibox326 k).hi-(ibox326 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox326
    (computed denominator ibox326) (computed denominator (FixedTape.midBox ibox326))
    (by decide +kernel)
private theorem midpoint_even_326 : ∀ k, 2 ∣ (ibox326 k).lo+(ibox326 k).hi := by decide +kernel
private theorem accepted_326 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox326) tree326 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox326 midpoint_even_326
  simp only [tree326,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox326,candidate_valid h (FixedTape.midBox ibox326),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox326 101 (FixedTape.rowsAux denominator ibox326 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox326) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_326
private noncomputable def tree325 : TapeTree := .split 1 (((405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree326 tree327
attribute [irreducible] tree325
private theorem accepted_325 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox325) tree325 = true := by
  simp only [tree325,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox325 1 (405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) false,decode_split denominator ibox325 1 (405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_326 h,accepted_327 h⟩
private noncomputable def tree324 : TapeTree := .centered (candidateRows ibox324) (candidateRows (FixedTape.midBox ibox324))
attribute [irreducible] tree324
private theorem sign_324 : 2*denominator*(computed denominator (FixedTape.midBox ibox324)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox324).gradient k).lo.natAbs ((computed denominator ibox324).gradient k).hi.natAbs : Int)*((ibox324 k).hi-(ibox324 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox324
    (computed denominator ibox324) (computed denominator (FixedTape.midBox ibox324))
    (by decide +kernel)
private theorem midpoint_even_324 : ∀ k, 2 ∣ (ibox324 k).lo+(ibox324 k).hi := by decide +kernel
private theorem accepted_324 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox324) tree324 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox324 midpoint_even_324
  simp only [tree324,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox324,candidate_valid h (FixedTape.midBox ibox324),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox324 101 (FixedTape.rowsAux denominator ibox324 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox324) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_324
private noncomputable def tree323 : TapeTree := .centered (candidateRows ibox323) (candidateRows (FixedTape.midBox ibox323))
attribute [irreducible] tree323
private theorem sign_323 : 2*denominator*(computed denominator (FixedTape.midBox ibox323)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox323).gradient k).lo.natAbs ((computed denominator ibox323).gradient k).hi.natAbs : Int)*((ibox323 k).hi-(ibox323 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox323
    (computed denominator ibox323) (computed denominator (FixedTape.midBox ibox323))
    (by decide +kernel)
private theorem midpoint_even_323 : ∀ k, 2 ∣ (ibox323 k).lo+(ibox323 k).hi := by decide +kernel
private theorem accepted_323 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox323) tree323 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox323 midpoint_even_323
  simp only [tree323,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox323,candidate_valid h (FixedTape.midBox ibox323),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox323 101 (FixedTape.rowsAux denominator ibox323 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox323) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_323
private noncomputable def tree322 : TapeTree := .split 1 (((405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree323 tree324
attribute [irreducible] tree322
private theorem accepted_322 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox322) tree322 = true := by
  simp only [tree322,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox322 1 (405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) false,decode_split denominator ibox322 1 (405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_323 h,accepted_324 h⟩
private noncomputable def tree321 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree322 tree325
attribute [irreducible] tree321
private theorem accepted_321 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox321) tree321 = true := by
  simp only [tree321,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox321 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox321 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_322 h,accepted_325 h⟩
private noncomputable def tree320 : TapeTree := .centered (candidateRows ibox320) (candidateRows (FixedTape.midBox ibox320))
attribute [irreducible] tree320
private theorem sign_320 : 2*denominator*(computed denominator (FixedTape.midBox ibox320)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox320).gradient k).lo.natAbs ((computed denominator ibox320).gradient k).hi.natAbs : Int)*((ibox320 k).hi-(ibox320 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox320
    (computed denominator ibox320) (computed denominator (FixedTape.midBox ibox320))
    (by decide +kernel)
private theorem midpoint_even_320 : ∀ k, 2 ∣ (ibox320 k).lo+(ibox320 k).hi := by decide +kernel
private theorem accepted_320 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox320) tree320 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox320 midpoint_even_320
  simp only [tree320,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox320,candidate_valid h (FixedTape.midBox ibox320),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox320 101 (FixedTape.rowsAux denominator ibox320 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox320) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_320
private noncomputable def tree319 : TapeTree := .centered (candidateRows ibox319) (candidateRows (FixedTape.midBox ibox319))
attribute [irreducible] tree319
private theorem sign_319 : 2*denominator*(computed denominator (FixedTape.midBox ibox319)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox319).gradient k).lo.natAbs ((computed denominator ibox319).gradient k).hi.natAbs : Int)*((ibox319 k).hi-(ibox319 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox319
    (computed denominator ibox319) (computed denominator (FixedTape.midBox ibox319))
    (by decide +kernel)
private theorem midpoint_even_319 : ∀ k, 2 ∣ (ibox319 k).lo+(ibox319 k).hi := by decide +kernel
private theorem accepted_319 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox319) tree319 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox319 midpoint_even_319
  simp only [tree319,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox319,candidate_valid h (FixedTape.midBox ibox319),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox319 101 (FixedTape.rowsAux denominator ibox319 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox319) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_319
private noncomputable def tree318 : TapeTree := .split 1 (((351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree319 tree320
attribute [irreducible] tree318
private theorem accepted_318 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox318) tree318 = true := by
  simp only [tree318,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox318 1 (351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) false,decode_split denominator ibox318 1 (351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_319 h,accepted_320 h⟩
private noncomputable def tree317 : TapeTree := .centered (candidateRows ibox317) (candidateRows (FixedTape.midBox ibox317))
attribute [irreducible] tree317
private theorem sign_317 : 2*denominator*(computed denominator (FixedTape.midBox ibox317)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox317).gradient k).lo.natAbs ((computed denominator ibox317).gradient k).hi.natAbs : Int)*((ibox317 k).hi-(ibox317 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox317
    (computed denominator ibox317) (computed denominator (FixedTape.midBox ibox317))
    (by decide +kernel)
private theorem midpoint_even_317 : ∀ k, 2 ∣ (ibox317 k).lo+(ibox317 k).hi := by decide +kernel
private theorem accepted_317 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox317) tree317 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox317 midpoint_even_317
  simp only [tree317,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox317,candidate_valid h (FixedTape.midBox ibox317),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox317 101 (FixedTape.rowsAux denominator ibox317 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox317) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_317
private noncomputable def tree316 : TapeTree := .centered (candidateRows ibox316) (candidateRows (FixedTape.midBox ibox316))
attribute [irreducible] tree316
private theorem sign_316 : 2*denominator*(computed denominator (FixedTape.midBox ibox316)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox316).gradient k).lo.natAbs ((computed denominator ibox316).gradient k).hi.natAbs : Int)*((ibox316 k).hi-(ibox316 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox316
    (computed denominator ibox316) (computed denominator (FixedTape.midBox ibox316))
    (by decide +kernel)
private theorem midpoint_even_316 : ∀ k, 2 ∣ (ibox316 k).lo+(ibox316 k).hi := by decide +kernel
private theorem accepted_316 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox316) tree316 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox316 midpoint_even_316
  simp only [tree316,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox316,candidate_valid h (FixedTape.midBox ibox316),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox316 101 (FixedTape.rowsAux denominator ibox316 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox316) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_316
private noncomputable def tree315 : TapeTree := .split 1 (((351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree316 tree317
attribute [irreducible] tree315
private theorem accepted_315 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox315) tree315 = true := by
  simp only [tree315,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox315 1 (351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) false,decode_split denominator ibox315 1 (351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_316 h,accepted_317 h⟩
private noncomputable def tree314 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree315 tree318
attribute [irreducible] tree314
private theorem accepted_314 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox314) tree314 = true := by
  simp only [tree314,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox314 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox314 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_315 h,accepted_318 h⟩
private noncomputable def tree313 : TapeTree := .split 1 (((378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree314 tree321
attribute [irreducible] tree313
private theorem accepted_313 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox313) tree313 = true := by
  simp only [tree313,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox313 1 (378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 : Int) false,decode_split denominator ibox313 1 (378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_314 h,accepted_321 h⟩
private noncomputable def tree312 : TapeTree := .centered (candidateRows ibox312) (candidateRows (FixedTape.midBox ibox312))
attribute [irreducible] tree312
private theorem sign_312 : 2*denominator*(computed denominator (FixedTape.midBox ibox312)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox312).gradient k).lo.natAbs ((computed denominator ibox312).gradient k).hi.natAbs : Int)*((ibox312 k).hi-(ibox312 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox312
    (computed denominator ibox312) (computed denominator (FixedTape.midBox ibox312))
    (by decide +kernel)
private theorem midpoint_even_312 : ∀ k, 2 ∣ (ibox312 k).lo+(ibox312 k).hi := by decide +kernel
private theorem accepted_312 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox312) tree312 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox312 midpoint_even_312
  simp only [tree312,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox312,candidate_valid h (FixedTape.midBox ibox312),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox312 101 (FixedTape.rowsAux denominator ibox312 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox312) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_312
private noncomputable def tree311 : TapeTree := .centered (candidateRows ibox311) (candidateRows (FixedTape.midBox ibox311))
attribute [irreducible] tree311
private theorem sign_311 : 2*denominator*(computed denominator (FixedTape.midBox ibox311)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox311).gradient k).lo.natAbs ((computed denominator ibox311).gradient k).hi.natAbs : Int)*((ibox311 k).hi-(ibox311 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox311
    (computed denominator ibox311) (computed denominator (FixedTape.midBox ibox311))
    (by decide +kernel)
private theorem midpoint_even_311 : ∀ k, 2 ∣ (ibox311 k).lo+(ibox311 k).hi := by decide +kernel
private theorem accepted_311 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox311) tree311 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox311 midpoint_even_311
  simp only [tree311,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox311,candidate_valid h (FixedTape.midBox ibox311),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox311 101 (FixedTape.rowsAux denominator ibox311 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox311) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_311
private noncomputable def tree310 : TapeTree := .split 1 (((297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree311 tree312
attribute [irreducible] tree310
private theorem accepted_310 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox310) tree310 = true := by
  simp only [tree310,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox310 1 (297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) false,decode_split denominator ibox310 1 (297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_311 h,accepted_312 h⟩
private noncomputable def tree309 : TapeTree := .centered (candidateRows ibox309) (candidateRows (FixedTape.midBox ibox309))
attribute [irreducible] tree309
private theorem sign_309 : 2*denominator*(computed denominator (FixedTape.midBox ibox309)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox309).gradient k).lo.natAbs ((computed denominator ibox309).gradient k).hi.natAbs : Int)*((ibox309 k).hi-(ibox309 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox309
    (computed denominator ibox309) (computed denominator (FixedTape.midBox ibox309))
    (by decide +kernel)
private theorem midpoint_even_309 : ∀ k, 2 ∣ (ibox309 k).lo+(ibox309 k).hi := by decide +kernel
private theorem accepted_309 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox309) tree309 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox309 midpoint_even_309
  simp only [tree309,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox309,candidate_valid h (FixedTape.midBox ibox309),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox309 101 (FixedTape.rowsAux denominator ibox309 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox309) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_309
private noncomputable def tree308 : TapeTree := .centered (candidateRows ibox308) (candidateRows (FixedTape.midBox ibox308))
attribute [irreducible] tree308
private theorem sign_308 : 2*denominator*(computed denominator (FixedTape.midBox ibox308)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox308).gradient k).lo.natAbs ((computed denominator ibox308).gradient k).hi.natAbs : Int)*((ibox308 k).hi-(ibox308 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox308
    (computed denominator ibox308) (computed denominator (FixedTape.midBox ibox308))
    (by decide +kernel)
private theorem midpoint_even_308 : ∀ k, 2 ∣ (ibox308 k).lo+(ibox308 k).hi := by decide +kernel
private theorem accepted_308 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox308) tree308 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox308 midpoint_even_308
  simp only [tree308,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox308,candidate_valid h (FixedTape.midBox ibox308),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox308 101 (FixedTape.rowsAux denominator ibox308 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox308) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_308
private noncomputable def tree307 : TapeTree := .split 1 (((297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree308 tree309
attribute [irreducible] tree307
private theorem accepted_307 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox307) tree307 = true := by
  simp only [tree307,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox307 1 (297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) false,decode_split denominator ibox307 1 (297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_308 h,accepted_309 h⟩
private noncomputable def tree306 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree307 tree310
attribute [irreducible] tree306
private theorem accepted_306 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox306) tree306 = true := by
  simp only [tree306,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox306 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox306 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_307 h,accepted_310 h⟩
private noncomputable def tree305 : TapeTree := .centered (candidateRows ibox305) (candidateRows (FixedTape.midBox ibox305))
attribute [irreducible] tree305
private theorem sign_305 : 2*denominator*(computed denominator (FixedTape.midBox ibox305)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox305).gradient k).lo.natAbs ((computed denominator ibox305).gradient k).hi.natAbs : Int)*((ibox305 k).hi-(ibox305 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox305
    (computed denominator ibox305) (computed denominator (FixedTape.midBox ibox305))
    (by decide +kernel)
private theorem midpoint_even_305 : ∀ k, 2 ∣ (ibox305 k).lo+(ibox305 k).hi := by decide +kernel
private theorem accepted_305 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox305) tree305 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox305 midpoint_even_305
  simp only [tree305,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox305,candidate_valid h (FixedTape.midBox ibox305),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox305 101 (FixedTape.rowsAux denominator ibox305 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox305) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_305
private noncomputable def tree304 : TapeTree := .centered (candidateRows ibox304) (candidateRows (FixedTape.midBox ibox304))
attribute [irreducible] tree304
private theorem sign_304 : 2*denominator*(computed denominator (FixedTape.midBox ibox304)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox304).gradient k).lo.natAbs ((computed denominator ibox304).gradient k).hi.natAbs : Int)*((ibox304 k).hi-(ibox304 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox304
    (computed denominator ibox304) (computed denominator (FixedTape.midBox ibox304))
    (by decide +kernel)
private theorem midpoint_even_304 : ∀ k, 2 ∣ (ibox304 k).lo+(ibox304 k).hi := by decide +kernel
private theorem accepted_304 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox304) tree304 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox304 midpoint_even_304
  simp only [tree304,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox304,candidate_valid h (FixedTape.midBox ibox304),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox304 101 (FixedTape.rowsAux denominator ibox304 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox304) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_304
private noncomputable def tree303 : TapeTree := .split 1 (((243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree304 tree305
attribute [irreducible] tree303
private theorem accepted_303 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox303) tree303 = true := by
  simp only [tree303,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox303 1 (243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) false,decode_split denominator ibox303 1 (243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_304 h,accepted_305 h⟩
private noncomputable def tree302 : TapeTree := .centered (candidateRows ibox302) (candidateRows (FixedTape.midBox ibox302))
attribute [irreducible] tree302
private theorem sign_302 : 2*denominator*(computed denominator (FixedTape.midBox ibox302)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox302).gradient k).lo.natAbs ((computed denominator ibox302).gradient k).hi.natAbs : Int)*((ibox302 k).hi-(ibox302 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox302
    (computed denominator ibox302) (computed denominator (FixedTape.midBox ibox302))
    (by decide +kernel)
private theorem midpoint_even_302 : ∀ k, 2 ∣ (ibox302 k).lo+(ibox302 k).hi := by decide +kernel
private theorem accepted_302 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox302) tree302 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox302 midpoint_even_302
  simp only [tree302,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox302,candidate_valid h (FixedTape.midBox ibox302),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox302 101 (FixedTape.rowsAux denominator ibox302 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox302) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_302
private noncomputable def tree301 : TapeTree := .centered (candidateRows ibox301) (candidateRows (FixedTape.midBox ibox301))
attribute [irreducible] tree301
private theorem sign_301 : 2*denominator*(computed denominator (FixedTape.midBox ibox301)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox301).gradient k).lo.natAbs ((computed denominator ibox301).gradient k).hi.natAbs : Int)*((ibox301 k).hi-(ibox301 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox301
    (computed denominator ibox301) (computed denominator (FixedTape.midBox ibox301))
    (by decide +kernel)
private theorem midpoint_even_301 : ∀ k, 2 ∣ (ibox301 k).lo+(ibox301 k).hi := by decide +kernel
private theorem accepted_301 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox301) tree301 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox301 midpoint_even_301
  simp only [tree301,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox301,candidate_valid h (FixedTape.midBox ibox301),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox301 101 (FixedTape.rowsAux denominator ibox301 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox301) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_301
private noncomputable def tree300 : TapeTree := .split 1 (((243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree301 tree302
attribute [irreducible] tree300
private theorem accepted_300 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox300) tree300 = true := by
  simp only [tree300,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox300 1 (243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) false,decode_split denominator ibox300 1 (243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_301 h,accepted_302 h⟩
private noncomputable def tree299 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree300 tree303
attribute [irreducible] tree299
private theorem accepted_299 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox299) tree299 = true := by
  simp only [tree299,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox299 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox299 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_300 h,accepted_303 h⟩
private noncomputable def tree298 : TapeTree := .split 1 (((270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree299 tree306
attribute [irreducible] tree298
private theorem accepted_298 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox298) tree298 = true := by
  simp only [tree298,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox298 1 (270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 : Int) false,decode_split denominator ibox298 1 (270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_299 h,accepted_306 h⟩
private noncomputable def tree297 : TapeTree := .split 1 (((324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree298 tree313
attribute [irreducible] tree297
private theorem accepted_297 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox297) tree297 = true := by
  simp only [tree297,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox297 1 (324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 : Int) false,decode_split denominator ibox297 1 (324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_298 h,accepted_313 h⟩
private noncomputable def tree296 : TapeTree := .centered (candidateRows ibox296) (candidateRows (FixedTape.midBox ibox296))
attribute [irreducible] tree296
private theorem sign_296 : 2*denominator*(computed denominator (FixedTape.midBox ibox296)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox296).gradient k).lo.natAbs ((computed denominator ibox296).gradient k).hi.natAbs : Int)*((ibox296 k).hi-(ibox296 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox296
    (computed denominator ibox296) (computed denominator (FixedTape.midBox ibox296))
    (by decide +kernel)
private theorem midpoint_even_296 : ∀ k, 2 ∣ (ibox296 k).lo+(ibox296 k).hi := by decide +kernel
private theorem accepted_296 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox296) tree296 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox296 midpoint_even_296
  simp only [tree296,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox296,candidate_valid h (FixedTape.midBox ibox296),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox296 101 (FixedTape.rowsAux denominator ibox296 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox296) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_296
private noncomputable def tree295 : TapeTree := .centered (candidateRows ibox295) (candidateRows (FixedTape.midBox ibox295))
attribute [irreducible] tree295
private theorem sign_295 : 2*denominator*(computed denominator (FixedTape.midBox ibox295)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox295).gradient k).lo.natAbs ((computed denominator ibox295).gradient k).hi.natAbs : Int)*((ibox295 k).hi-(ibox295 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox295
    (computed denominator ibox295) (computed denominator (FixedTape.midBox ibox295))
    (by decide +kernel)
private theorem midpoint_even_295 : ∀ k, 2 ∣ (ibox295 k).lo+(ibox295 k).hi := by decide +kernel
private theorem accepted_295 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox295) tree295 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox295 midpoint_even_295
  simp only [tree295,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox295,candidate_valid h (FixedTape.midBox ibox295),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox295 101 (FixedTape.rowsAux denominator ibox295 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox295) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_295
private noncomputable def tree294 : TapeTree := .split 1 (((189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree295 tree296
attribute [irreducible] tree294
private theorem accepted_294 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox294) tree294 = true := by
  simp only [tree294,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox294 1 (189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) false,decode_split denominator ibox294 1 (189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_295 h,accepted_296 h⟩
private noncomputable def tree293 : TapeTree := .centered (candidateRows ibox293) (candidateRows (FixedTape.midBox ibox293))
attribute [irreducible] tree293
private theorem sign_293 : 2*denominator*(computed denominator (FixedTape.midBox ibox293)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox293).gradient k).lo.natAbs ((computed denominator ibox293).gradient k).hi.natAbs : Int)*((ibox293 k).hi-(ibox293 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox293
    (computed denominator ibox293) (computed denominator (FixedTape.midBox ibox293))
    (by decide +kernel)
private theorem midpoint_even_293 : ∀ k, 2 ∣ (ibox293 k).lo+(ibox293 k).hi := by decide +kernel
private theorem accepted_293 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox293) tree293 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox293 midpoint_even_293
  simp only [tree293,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox293,candidate_valid h (FixedTape.midBox ibox293),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox293 101 (FixedTape.rowsAux denominator ibox293 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox293) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_293
private noncomputable def tree292 : TapeTree := .centered (candidateRows ibox292) (candidateRows (FixedTape.midBox ibox292))
attribute [irreducible] tree292
private theorem sign_292 : 2*denominator*(computed denominator (FixedTape.midBox ibox292)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox292).gradient k).lo.natAbs ((computed denominator ibox292).gradient k).hi.natAbs : Int)*((ibox292 k).hi-(ibox292 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox292
    (computed denominator ibox292) (computed denominator (FixedTape.midBox ibox292))
    (by decide +kernel)
private theorem midpoint_even_292 : ∀ k, 2 ∣ (ibox292 k).lo+(ibox292 k).hi := by decide +kernel
private theorem accepted_292 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox292) tree292 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox292 midpoint_even_292
  simp only [tree292,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox292,candidate_valid h (FixedTape.midBox ibox292),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox292 101 (FixedTape.rowsAux denominator ibox292 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox292) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_292
private noncomputable def tree291 : TapeTree := .split 1 (((189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree292 tree293
attribute [irreducible] tree291
private theorem accepted_291 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox291) tree291 = true := by
  simp only [tree291,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox291 1 (189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) false,decode_split denominator ibox291 1 (189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_292 h,accepted_293 h⟩
private noncomputable def tree290 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree291 tree294
attribute [irreducible] tree290
private theorem accepted_290 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox290) tree290 = true := by
  simp only [tree290,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox290 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox290 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_291 h,accepted_294 h⟩
private noncomputable def tree289 : TapeTree := .centered (candidateRows ibox289) (candidateRows (FixedTape.midBox ibox289))
attribute [irreducible] tree289
private theorem sign_289 : 2*denominator*(computed denominator (FixedTape.midBox ibox289)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox289).gradient k).lo.natAbs ((computed denominator ibox289).gradient k).hi.natAbs : Int)*((ibox289 k).hi-(ibox289 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox289
    (computed denominator ibox289) (computed denominator (FixedTape.midBox ibox289))
    (by decide +kernel)
private theorem midpoint_even_289 : ∀ k, 2 ∣ (ibox289 k).lo+(ibox289 k).hi := by decide +kernel
private theorem accepted_289 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox289) tree289 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox289 midpoint_even_289
  simp only [tree289,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox289,candidate_valid h (FixedTape.midBox ibox289),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox289 101 (FixedTape.rowsAux denominator ibox289 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox289) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_289
private noncomputable def tree288 : TapeTree := .centered (candidateRows ibox288) (candidateRows (FixedTape.midBox ibox288))
attribute [irreducible] tree288
private theorem sign_288 : 2*denominator*(computed denominator (FixedTape.midBox ibox288)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox288).gradient k).lo.natAbs ((computed denominator ibox288).gradient k).hi.natAbs : Int)*((ibox288 k).hi-(ibox288 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox288
    (computed denominator ibox288) (computed denominator (FixedTape.midBox ibox288))
    (by decide +kernel)
private theorem midpoint_even_288 : ∀ k, 2 ∣ (ibox288 k).lo+(ibox288 k).hi := by decide +kernel
private theorem accepted_288 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox288) tree288 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox288 midpoint_even_288
  simp only [tree288,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox288,candidate_valid h (FixedTape.midBox ibox288),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox288 101 (FixedTape.rowsAux denominator ibox288 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox288) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_288
private noncomputable def tree287 : TapeTree := .split 1 (((135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree288 tree289
attribute [irreducible] tree287
private theorem accepted_287 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox287) tree287 = true := by
  simp only [tree287,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox287 1 (135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) false,decode_split denominator ibox287 1 (135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_288 h,accepted_289 h⟩
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
private noncomputable def tree285 : TapeTree := .centered (candidateRows ibox285) (candidateRows (FixedTape.midBox ibox285))
attribute [irreducible] tree285
private theorem sign_285 : 2*denominator*(computed denominator (FixedTape.midBox ibox285)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox285).gradient k).lo.natAbs ((computed denominator ibox285).gradient k).hi.natAbs : Int)*((ibox285 k).hi-(ibox285 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox285
    (computed denominator ibox285) (computed denominator (FixedTape.midBox ibox285))
    (by decide +kernel)
private theorem midpoint_even_285 : ∀ k, 2 ∣ (ibox285 k).lo+(ibox285 k).hi := by decide +kernel
private theorem accepted_285 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox285) tree285 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox285 midpoint_even_285
  simp only [tree285,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox285,candidate_valid h (FixedTape.midBox ibox285),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox285 101 (FixedTape.rowsAux denominator ibox285 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox285) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_285
private noncomputable def tree284 : TapeTree := .split 1 (((135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree285 tree286
attribute [irreducible] tree284
private theorem accepted_284 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox284) tree284 = true := by
  simp only [tree284,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox284 1 (135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) false,decode_split denominator ibox284 1 (135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_285 h,accepted_286 h⟩
private noncomputable def tree283 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree284 tree287
attribute [irreducible] tree283
private theorem accepted_283 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox283) tree283 = true := by
  simp only [tree283,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox283 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox283 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_284 h,accepted_287 h⟩
private noncomputable def tree282 : TapeTree := .split 1 (((162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree283 tree290
attribute [irreducible] tree282
private theorem accepted_282 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox282) tree282 = true := by
  simp only [tree282,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox282 1 (162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 : Int) false,decode_split denominator ibox282 1 (162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_283 h,accepted_290 h⟩
private noncomputable def tree281 : TapeTree := .centered (candidateRows ibox281) (candidateRows (FixedTape.midBox ibox281))
attribute [irreducible] tree281
private theorem sign_281 : 2*denominator*(computed denominator (FixedTape.midBox ibox281)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox281).gradient k).lo.natAbs ((computed denominator ibox281).gradient k).hi.natAbs : Int)*((ibox281 k).hi-(ibox281 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox281
    (computed denominator ibox281) (computed denominator (FixedTape.midBox ibox281))
    (by decide +kernel)
private theorem midpoint_even_281 : ∀ k, 2 ∣ (ibox281 k).lo+(ibox281 k).hi := by decide +kernel
private theorem accepted_281 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox281) tree281 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox281 midpoint_even_281
  simp only [tree281,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox281,candidate_valid h (FixedTape.midBox ibox281),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox281 101 (FixedTape.rowsAux denominator ibox281 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox281) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_281
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
private noncomputable def tree279 : TapeTree := .split 1 (((81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree280 tree281
attribute [irreducible] tree279
private theorem accepted_279 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox279) tree279 = true := by
  simp only [tree279,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox279 1 (81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) false,decode_split denominator ibox279 1 (81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_280 h,accepted_281 h⟩
private noncomputable def tree278 : TapeTree := .centered (candidateRows ibox278) (candidateRows (FixedTape.midBox ibox278))
attribute [irreducible] tree278
private theorem sign_278 : 2*denominator*(computed denominator (FixedTape.midBox ibox278)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox278).gradient k).lo.natAbs ((computed denominator ibox278).gradient k).hi.natAbs : Int)*((ibox278 k).hi-(ibox278 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox278
    (computed denominator ibox278) (computed denominator (FixedTape.midBox ibox278))
    (by decide +kernel)
private theorem midpoint_even_278 : ∀ k, 2 ∣ (ibox278 k).lo+(ibox278 k).hi := by decide +kernel
private theorem accepted_278 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox278) tree278 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox278 midpoint_even_278
  simp only [tree278,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox278,candidate_valid h (FixedTape.midBox ibox278),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox278 101 (FixedTape.rowsAux denominator ibox278 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox278) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_278
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
private noncomputable def tree276 : TapeTree := .split 1 (((81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree277 tree278
attribute [irreducible] tree276
private theorem accepted_276 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox276) tree276 = true := by
  simp only [tree276,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox276 1 (81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) false,decode_split denominator ibox276 1 (81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_277 h,accepted_278 h⟩
private noncomputable def tree275 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree276 tree279
attribute [irreducible] tree275
private theorem accepted_275 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox275) tree275 = true := by
  simp only [tree275,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox275 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox275 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_276 h,accepted_279 h⟩
private noncomputable def tree274 : TapeTree := .centered (candidateRows ibox274) (candidateRows (FixedTape.midBox ibox274))
attribute [irreducible] tree274
private theorem sign_274 : 2*denominator*(computed denominator (FixedTape.midBox ibox274)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox274).gradient k).lo.natAbs ((computed denominator ibox274).gradient k).hi.natAbs : Int)*((ibox274 k).hi-(ibox274 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox274
    (computed denominator ibox274) (computed denominator (FixedTape.midBox ibox274))
    (by decide +kernel)
private theorem midpoint_even_274 : ∀ k, 2 ∣ (ibox274 k).lo+(ibox274 k).hi := by decide +kernel
private theorem accepted_274 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox274) tree274 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox274 midpoint_even_274
  simp only [tree274,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox274,candidate_valid h (FixedTape.midBox ibox274),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox274 101 (FixedTape.rowsAux denominator ibox274 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox274) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_274
private noncomputable def tree273 : TapeTree := .centered (candidateRows ibox273) (candidateRows (FixedTape.midBox ibox273))
attribute [irreducible] tree273
private theorem sign_273 : 2*denominator*(computed denominator (FixedTape.midBox ibox273)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox273).gradient k).lo.natAbs ((computed denominator ibox273).gradient k).hi.natAbs : Int)*((ibox273 k).hi-(ibox273 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox273
    (computed denominator ibox273) (computed denominator (FixedTape.midBox ibox273))
    (by decide +kernel)
private theorem midpoint_even_273 : ∀ k, 2 ∣ (ibox273 k).lo+(ibox273 k).hi := by decide +kernel
private theorem accepted_273 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox273) tree273 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox273 midpoint_even_273
  simp only [tree273,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox273,candidate_valid h (FixedTape.midBox ibox273),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox273 101 (FixedTape.rowsAux denominator ibox273 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox273) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_273
private noncomputable def tree272 : TapeTree := .split 1 (((27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree273 tree274
attribute [irreducible] tree272
private theorem accepted_272 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox272) tree272 = true := by
  simp only [tree272,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox272 1 (27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) false,decode_split denominator ibox272 1 (27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_273 h,accepted_274 h⟩
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
private noncomputable def tree270 : TapeTree := .centered (candidateRows ibox270) (candidateRows (FixedTape.midBox ibox270))
attribute [irreducible] tree270
private theorem sign_270 : 2*denominator*(computed denominator (FixedTape.midBox ibox270)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox270).gradient k).lo.natAbs ((computed denominator ibox270).gradient k).hi.natAbs : Int)*((ibox270 k).hi-(ibox270 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox270
    (computed denominator ibox270) (computed denominator (FixedTape.midBox ibox270))
    (by decide +kernel)
private theorem midpoint_even_270 : ∀ k, 2 ∣ (ibox270 k).lo+(ibox270 k).hi := by decide +kernel
private theorem accepted_270 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox270) tree270 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox270 midpoint_even_270
  simp only [tree270,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox270,candidate_valid h (FixedTape.midBox ibox270),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox270 101 (FixedTape.rowsAux denominator ibox270 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox270) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_270
private noncomputable def tree269 : TapeTree := .split 1 (((27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree270 tree271
attribute [irreducible] tree269
private theorem accepted_269 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox269) tree269 = true := by
  simp only [tree269,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox269 1 (27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) false,decode_split denominator ibox269 1 (27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_270 h,accepted_271 h⟩
private noncomputable def tree268 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree269 tree272
attribute [irreducible] tree268
private theorem accepted_268 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox268) tree268 = true := by
  simp only [tree268,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox268 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox268 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_269 h,accepted_272 h⟩
private noncomputable def tree267 : TapeTree := .split 1 (((54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree268 tree275
attribute [irreducible] tree267
private theorem accepted_267 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox267) tree267 = true := by
  simp only [tree267,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox267 1 (54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 : Int) false,decode_split denominator ibox267 1 (54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_268 h,accepted_275 h⟩
private noncomputable def tree266 : TapeTree := .split 1 (((108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree267 tree282
attribute [irreducible] tree266
private theorem accepted_266 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox266) tree266 = true := by
  simp only [tree266,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox266 1 (108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 : Int) false,decode_split denominator ibox266 1 (108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_267 h,accepted_282 h⟩
private noncomputable def tree265 : TapeTree := .split 1 (((216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree266 tree297
attribute [irreducible] tree265
private theorem accepted_265 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox265) tree265 = true := by
  simp only [tree265,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox265 1 (216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 : Int) false,decode_split denominator ibox265 1 (216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_266 h,accepted_297 h⟩
private noncomputable def tree264 : TapeTree := .split 2 (((757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree265 tree328
attribute [irreducible] tree264
private theorem accepted_264 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox264) tree264 = true := by
  simp only [tree264,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox264 2 (757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 : Int) false,decode_split denominator ibox264 2 (757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_265 h,accepted_328 h⟩
private noncomputable def tree263 : TapeTree := .split 1 (((432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree264 tree487
attribute [irreducible] tree263
private theorem accepted_263 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox263) tree263 = true := by
  simp only [tree263,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox263 1 (432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 : Int) false,decode_split denominator ibox263 1 (432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_264 h,accepted_487 h⟩
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
private noncomputable def tree260 : TapeTree := .split 1 (((851842533989001325293623708861207859381663597994136796223825191213465600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree261 tree262
attribute [irreducible] tree260
private theorem accepted_260 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox260) tree260 = true := by
  simp only [tree260,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox260 1 (851842533989001325293623708861207859381663597994136796223825191213465600000000000000000000000 : Int) false,decode_split denominator ibox260 1 (851842533989001325293623708861207859381663597994136796223825191213465600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_261 h,accepted_262 h⟩
private noncomputable def tree259 : TapeTree := .centered (candidateRows ibox259) (candidateRows (FixedTape.midBox ibox259))
attribute [irreducible] tree259
private theorem sign_259 : 2*denominator*(computed denominator (FixedTape.midBox ibox259)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox259).gradient k).lo.natAbs ((computed denominator ibox259).gradient k).hi.natAbs : Int)*((ibox259 k).hi-(ibox259 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox259
    (computed denominator ibox259) (computed denominator (FixedTape.midBox ibox259))
    (by decide +kernel)
private theorem midpoint_even_259 : ∀ k, 2 ∣ (ibox259 k).lo+(ibox259 k).hi := by decide +kernel
private theorem accepted_259 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox259) tree259 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox259 midpoint_even_259
  simp only [tree259,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox259,candidate_valid h (FixedTape.midBox ibox259),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox259 101 (FixedTape.rowsAux denominator ibox259 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox259) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_259
private noncomputable def tree258 : TapeTree := .centered (candidateRows ibox258) (candidateRows (FixedTape.midBox ibox258))
attribute [irreducible] tree258
private theorem sign_258 : 2*denominator*(computed denominator (FixedTape.midBox ibox258)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox258).gradient k).lo.natAbs ((computed denominator ibox258).gradient k).hi.natAbs : Int)*((ibox258 k).hi-(ibox258 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox258
    (computed denominator ibox258) (computed denominator (FixedTape.midBox ibox258))
    (by decide +kernel)
private theorem midpoint_even_258 : ∀ k, 2 ∣ (ibox258 k).lo+(ibox258 k).hi := by decide +kernel
private theorem accepted_258 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox258) tree258 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox258 midpoint_even_258
  simp only [tree258,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox258,candidate_valid h (FixedTape.midBox ibox258),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox258 101 (FixedTape.rowsAux denominator ibox258 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox258) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_258
private noncomputable def tree257 : TapeTree := .split 1 (((824799913862366362585889622865613959083833007581624516978624391492403200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree258 tree259
attribute [irreducible] tree257
private theorem accepted_257 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox257) tree257 = true := by
  simp only [tree257,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox257 1 (824799913862366362585889622865613959083833007581624516978624391492403200000000000000000000000 : Int) false,decode_split denominator ibox257 1 (824799913862366362585889622865613959083833007581624516978624391492403200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_258 h,accepted_259 h⟩
private noncomputable def tree256 : TapeTree := .split 1 (((838321223925683843939756665863410909232748302787880656601224791352934400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree257 tree260
attribute [irreducible] tree256
private theorem accepted_256 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox256) tree256 = true := by
  simp only [tree256,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox256 1 (838321223925683843939756665863410909232748302787880656601224791352934400000000000000000000000 : Int) false,decode_split denominator ibox256 1 (838321223925683843939756665863410909232748302787880656601224791352934400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_257 h,accepted_260 h⟩
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
private noncomputable def tree254 : TapeTree := .centered (candidateRows ibox254) (candidateRows (FixedTape.midBox ibox254))
attribute [irreducible] tree254
private theorem sign_254 : 2*denominator*(computed denominator (FixedTape.midBox ibox254)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox254).gradient k).lo.natAbs ((computed denominator ibox254).gradient k).hi.natAbs : Int)*((ibox254 k).hi-(ibox254 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox254
    (computed denominator ibox254) (computed denominator (FixedTape.midBox ibox254))
    (by decide +kernel)
private theorem midpoint_even_254 : ∀ k, 2 ∣ (ibox254 k).lo+(ibox254 k).hi := by decide +kernel
private theorem accepted_254 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox254) tree254 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox254 midpoint_even_254
  simp only [tree254,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox254,candidate_valid h (FixedTape.midBox ibox254),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox254 101 (FixedTape.rowsAux denominator ibox254 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox254) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_254
private noncomputable def tree253 : TapeTree := .split 1 (((797757293735731399878155536870020058786002417169112237733423591771340800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree254 tree255
attribute [irreducible] tree253
private theorem accepted_253 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox253) tree253 = true := by
  simp only [tree253,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox253 1 (797757293735731399878155536870020058786002417169112237733423591771340800000000000000000000000 : Int) false,decode_split denominator ibox253 1 (797757293735731399878155536870020058786002417169112237733423591771340800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_254 h,accepted_255 h⟩
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
private noncomputable def tree250 : TapeTree := .split 1 (((770714673609096437170421450874426158488171826756599958488222792050278400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree251 tree252
attribute [irreducible] tree250
private theorem accepted_250 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox250) tree250 = true := by
  simp only [tree250,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox250 1 (770714673609096437170421450874426158488171826756599958488222792050278400000000000000000000000 : Int) false,decode_split denominator ibox250 1 (770714673609096437170421450874426158488171826756599958488222792050278400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_251 h,accepted_252 h⟩
private noncomputable def tree249 : TapeTree := .split 1 (((784235983672413918524288493872223108637087121962856098110823191910809600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree250 tree253
attribute [irreducible] tree249
private theorem accepted_249 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox249) tree249 = true := by
  simp only [tree249,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox249 1 (784235983672413918524288493872223108637087121962856098110823191910809600000000000000000000000 : Int) false,decode_split denominator ibox249 1 (784235983672413918524288493872223108637087121962856098110823191910809600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_250 h,accepted_253 h⟩
private noncomputable def tree248 : TapeTree := .split 1 (((811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree249 tree256
attribute [irreducible] tree248
private theorem accepted_248 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox248) tree248 = true := by
  simp only [tree248,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox248 1 (811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 : Int) false,decode_split denominator ibox248 1 (811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_249 h,accepted_256 h⟩
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
private noncomputable def tree245 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree246 tree247
attribute [irreducible] tree245
private theorem accepted_245 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox245) tree245 = true := by
  simp only [tree245,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox245 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox245 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
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
private noncomputable def tree242 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree243 tree244
attribute [irreducible] tree242
private theorem accepted_242 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox242) tree242 = true := by
  simp only [tree242,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox242 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox242 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_243 h,accepted_244 h⟩
private noncomputable def tree241 : TapeTree := .split 1 (((730150743419143993108820321881035308041425941137831539620421592468684800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree242 tree245
attribute [irreducible] tree241
private theorem accepted_241 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox241) tree241 = true := by
  simp only [tree241,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox241 1 (730150743419143993108820321881035308041425941137831539620421592468684800000000000000000000000 : Int) false,decode_split denominator ibox241 1 (730150743419143993108820321881035308041425941137831539620421592468684800000000000000000000000 : Int) true]
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
private noncomputable def tree238 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree239 tree240
attribute [irreducible] tree238
private theorem accepted_238 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox238) tree238 = true := by
  simp only [tree238,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox238 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox238 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
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
private noncomputable def tree235 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree236 tree237
attribute [irreducible] tree235
private theorem accepted_235 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox235) tree235 = true := by
  simp only [tree235,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox235 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox235 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_236 h,accepted_237 h⟩
private noncomputable def tree234 : TapeTree := .split 1 (((676065503165874067693352149889847507445764760312806981130019993026560000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree235 tree238
attribute [irreducible] tree234
private theorem accepted_234 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox234) tree234 = true := by
  simp only [tree234,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox234 1 (676065503165874067693352149889847507445764760312806981130019993026560000000000000000000000000 : Int) false,decode_split denominator ibox234 1 (676065503165874067693352149889847507445764760312806981130019993026560000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_235 h,accepted_238 h⟩
private noncomputable def tree233 : TapeTree := .split 1 (((703108123292509030401086235885441407743595350725319260375220792747622400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree234 tree241
attribute [irreducible] tree233
private theorem accepted_233 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox233) tree233 = true := by
  simp only [tree233,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox233 1 (703108123292509030401086235885441407743595350725319260375220792747622400000000000000000000000 : Int) false,decode_split denominator ibox233 1 (703108123292509030401086235885441407743595350725319260375220792747622400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_234 h,accepted_241 h⟩
private noncomputable def tree232 : TapeTree := .split 1 (((757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree233 tree248
attribute [irreducible] tree232
private theorem accepted_232 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox232) tree232 = true := by
  simp only [tree232,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox232 1 (757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 : Int) false,decode_split denominator ibox232 1 (757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 : Int) true]
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
private noncomputable def tree229 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree230 tree231
attribute [irreducible] tree229
private theorem accepted_229 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox229) tree229 = true := by
  simp only [tree229,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox229 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox229 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
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
private noncomputable def tree226 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree227 tree228
attribute [irreducible] tree226
private theorem accepted_226 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox226) tree226 = true := by
  simp only [tree226,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox226 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox226 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_227 h,accepted_228 h⟩
private noncomputable def tree225 : TapeTree := .centered (candidateRows ibox225) (candidateRows (FixedTape.midBox ibox225))
attribute [irreducible] tree225
private theorem sign_225 : 2*denominator*(computed denominator (FixedTape.midBox ibox225)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox225).gradient k).lo.natAbs ((computed denominator ibox225).gradient k).hi.natAbs : Int)*((ibox225 k).hi-(ibox225 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox225
    (computed denominator ibox225) (computed denominator (FixedTape.midBox ibox225))
    (by decide +kernel)
private theorem midpoint_even_225 : ∀ k, 2 ∣ (ibox225 k).lo+(ibox225 k).hi := by decide +kernel
private theorem accepted_225 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox225) tree225 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox225 midpoint_even_225
  simp only [tree225,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox225,candidate_valid h (FixedTape.midBox ibox225),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox225 101 (FixedTape.rowsAux denominator ibox225 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox225) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_225
private noncomputable def tree224 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree225 tree226
attribute [irreducible] tree224
private theorem accepted_224 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox224) tree224 = true := by
  simp only [tree224,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox224 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox224 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_225 h,accepted_226 h⟩
private noncomputable def tree223 : TapeTree := .split 1 (((621980262912604142277883977898659706850103579487782422639618393584435200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree224 tree229
attribute [irreducible] tree223
private theorem accepted_223 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox223) tree223 = true := by
  simp only [tree223,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox223 1 (621980262912604142277883977898659706850103579487782422639618393584435200000000000000000000000 : Int) false,decode_split denominator ibox223 1 (621980262912604142277883977898659706850103579487782422639618393584435200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_224 h,accepted_229 h⟩
private noncomputable def tree222 : TapeTree := .centered (candidateRows ibox222) (candidateRows (FixedTape.midBox ibox222))
attribute [irreducible] tree222
private theorem sign_222 : 2*denominator*(computed denominator (FixedTape.midBox ibox222)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox222).gradient k).lo.natAbs ((computed denominator ibox222).gradient k).hi.natAbs : Int)*((ibox222 k).hi-(ibox222 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox222
    (computed denominator ibox222) (computed denominator (FixedTape.midBox ibox222))
    (by decide +kernel)
private theorem midpoint_even_222 : ∀ k, 2 ∣ (ibox222 k).lo+(ibox222 k).hi := by decide +kernel
private theorem accepted_222 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox222) tree222 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox222 midpoint_even_222
  simp only [tree222,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox222,candidate_valid h (FixedTape.midBox ibox222),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox222 101 (FixedTape.rowsAux denominator ibox222 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox222) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_222
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
private noncomputable def tree220 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree221 tree222
attribute [irreducible] tree220
private theorem accepted_220 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox220) tree220 = true := by
  simp only [tree220,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox220 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox220 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_221 h,accepted_222 h⟩
private noncomputable def tree219 : TapeTree := .centered (candidateRows ibox219) (candidateRows (FixedTape.midBox ibox219))
attribute [irreducible] tree219
private theorem sign_219 : 2*denominator*(computed denominator (FixedTape.midBox ibox219)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox219).gradient k).lo.natAbs ((computed denominator ibox219).gradient k).hi.natAbs : Int)*((ibox219 k).hi-(ibox219 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox219
    (computed denominator ibox219) (computed denominator (FixedTape.midBox ibox219))
    (by decide +kernel)
private theorem midpoint_even_219 : ∀ k, 2 ∣ (ibox219 k).lo+(ibox219 k).hi := by decide +kernel
private theorem accepted_219 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox219) tree219 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox219 midpoint_even_219
  simp only [tree219,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox219,candidate_valid h (FixedTape.midBox ibox219),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox219 101 (FixedTape.rowsAux denominator ibox219 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox219) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_219
private noncomputable def tree218 : TapeTree := .centered (candidateRows ibox218) (candidateRows (FixedTape.midBox ibox218))
attribute [irreducible] tree218
private theorem sign_218 : 2*denominator*(computed denominator (FixedTape.midBox ibox218)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox218).gradient k).lo.natAbs ((computed denominator ibox218).gradient k).hi.natAbs : Int)*((ibox218 k).hi-(ibox218 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox218
    (computed denominator ibox218) (computed denominator (FixedTape.midBox ibox218))
    (by decide +kernel)
private theorem midpoint_even_218 : ∀ k, 2 ∣ (ibox218 k).lo+(ibox218 k).hi := by decide +kernel
private theorem accepted_218 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox218) tree218 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox218 midpoint_even_218
  simp only [tree218,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox218,candidate_valid h (FixedTape.midBox ibox218),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox218 101 (FixedTape.rowsAux denominator ibox218 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox218) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_218
private noncomputable def tree217 : TapeTree := .split 0 (((836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) : ℚ)/(denominator : ℚ)) tree218 tree219
attribute [irreducible] tree217
private theorem accepted_217 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox217) tree217 = true := by
  simp only [tree217,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox217 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) false,decode_split denominator ibox217 0 (836067672248464278136842892902424861666108284570251458840439611382728130773759851233280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_218 h,accepted_219 h⟩
private noncomputable def tree216 : TapeTree := .split 1 (((567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree217 tree220
attribute [irreducible] tree216
private theorem accepted_216 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox216) tree216 = true := by
  simp only [tree216,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox216 1 (567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 : Int) false,decode_split denominator ibox216 1 (567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_217 h,accepted_220 h⟩
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
private noncomputable def tree214 : TapeTree := .centered (candidateRows ibox214) (candidateRows (FixedTape.midBox ibox214))
attribute [irreducible] tree214
private theorem sign_214 : 2*denominator*(computed denominator (FixedTape.midBox ibox214)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox214).gradient k).lo.natAbs ((computed denominator ibox214).gradient k).hi.natAbs : Int)*((ibox214 k).hi-(ibox214 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox214
    (computed denominator ibox214) (computed denominator (FixedTape.midBox ibox214))
    (by decide +kernel)
private theorem midpoint_even_214 : ∀ k, 2 ∣ (ibox214 k).lo+(ibox214 k).hi := by decide +kernel
private theorem accepted_214 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox214) tree214 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox214 midpoint_even_214
  simp only [tree214,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox214,candidate_valid h (FixedTape.midBox ibox214),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox214 101 (FixedTape.rowsAux denominator ibox214 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox214) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_214
private noncomputable def tree213 : TapeTree := .split 1 (((567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree214 tree215
attribute [irreducible] tree213
private theorem accepted_213 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox213) tree213 = true := by
  simp only [tree213,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox213 1 (567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 : Int) false,decode_split denominator ibox213 1 (567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_214 h,accepted_215 h⟩
private noncomputable def tree212 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree213 tree216
attribute [irreducible] tree212
private theorem accepted_212 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox212) tree212 = true := by
  simp only [tree212,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox212 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox212 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_213 h,accepted_216 h⟩
private noncomputable def tree211 : TapeTree := .split 1 (((594937642785969179570149891903065806552272989075270143394417593863372800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree212 tree223
attribute [irreducible] tree211
private theorem accepted_211 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox211) tree211 = true := by
  simp only [tree211,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox211 1 (594937642785969179570149891903065806552272989075270143394417593863372800000000000000000000000 : Int) false,decode_split denominator ibox211 1 (594937642785969179570149891903065806552272989075270143394417593863372800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_212 h,accepted_223 h⟩
private noncomputable def tree210 : TapeTree := .centered (candidateRows ibox210) (candidateRows (FixedTape.midBox ibox210))
attribute [irreducible] tree210
private theorem sign_210 : 2*denominator*(computed denominator (FixedTape.midBox ibox210)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox210).gradient k).lo.natAbs ((computed denominator ibox210).gradient k).hi.natAbs : Int)*((ibox210 k).hi-(ibox210 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox210
    (computed denominator ibox210) (computed denominator (FixedTape.midBox ibox210))
    (by decide +kernel)
private theorem midpoint_even_210 : ∀ k, 2 ∣ (ibox210 k).lo+(ibox210 k).hi := by decide +kernel
private theorem accepted_210 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox210) tree210 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox210 midpoint_even_210
  simp only [tree210,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox210,candidate_valid h (FixedTape.midBox ibox210),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox210 101 (FixedTape.rowsAux denominator ibox210 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox210) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_210
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
private noncomputable def tree208 : TapeTree := .split 1 (((513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree209 tree210
attribute [irreducible] tree208
private theorem accepted_208 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox208) tree208 = true := by
  simp only [tree208,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox208 1 (513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 : Int) false,decode_split denominator ibox208 1 (513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_209 h,accepted_210 h⟩
private noncomputable def tree207 : TapeTree := .centered (candidateRows ibox207) (candidateRows (FixedTape.midBox ibox207))
attribute [irreducible] tree207
private theorem sign_207 : 2*denominator*(computed denominator (FixedTape.midBox ibox207)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox207).gradient k).lo.natAbs ((computed denominator ibox207).gradient k).hi.natAbs : Int)*((ibox207 k).hi-(ibox207 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox207
    (computed denominator ibox207) (computed denominator (FixedTape.midBox ibox207))
    (by decide +kernel)
private theorem midpoint_even_207 : ∀ k, 2 ∣ (ibox207 k).lo+(ibox207 k).hi := by decide +kernel
private theorem accepted_207 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox207) tree207 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox207 midpoint_even_207
  simp only [tree207,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox207,candidate_valid h (FixedTape.midBox ibox207),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox207 101 (FixedTape.rowsAux denominator ibox207 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox207) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_207
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
private noncomputable def tree205 : TapeTree := .split 1 (((513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree206 tree207
attribute [irreducible] tree205
private theorem accepted_205 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox205) tree205 = true := by
  simp only [tree205,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox205 1 (513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 : Int) false,decode_split denominator ibox205 1 (513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_206 h,accepted_207 h⟩
private noncomputable def tree204 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree205 tree208
attribute [irreducible] tree204
private theorem accepted_204 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox204) tree204 = true := by
  simp only [tree204,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox204 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox204 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_205 h,accepted_208 h⟩
private noncomputable def tree203 : TapeTree := .centered (candidateRows ibox203) (candidateRows (FixedTape.midBox ibox203))
attribute [irreducible] tree203
private theorem sign_203 : 2*denominator*(computed denominator (FixedTape.midBox ibox203)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox203).gradient k).lo.natAbs ((computed denominator ibox203).gradient k).hi.natAbs : Int)*((ibox203 k).hi-(ibox203 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox203
    (computed denominator ibox203) (computed denominator (FixedTape.midBox ibox203))
    (by decide +kernel)
private theorem midpoint_even_203 : ∀ k, 2 ∣ (ibox203 k).lo+(ibox203 k).hi := by decide +kernel
private theorem accepted_203 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox203) tree203 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox203 midpoint_even_203
  simp only [tree203,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox203,candidate_valid h (FixedTape.midBox ibox203),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox203 101 (FixedTape.rowsAux denominator ibox203 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox203) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_203
private noncomputable def tree202 : TapeTree := .centered (candidateRows ibox202) (candidateRows (FixedTape.midBox ibox202))
attribute [irreducible] tree202
private theorem sign_202 : 2*denominator*(computed denominator (FixedTape.midBox ibox202)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox202).gradient k).lo.natAbs ((computed denominator ibox202).gradient k).hi.natAbs : Int)*((ibox202 k).hi-(ibox202 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox202
    (computed denominator ibox202) (computed denominator (FixedTape.midBox ibox202))
    (by decide +kernel)
private theorem midpoint_even_202 : ∀ k, 2 ∣ (ibox202 k).lo+(ibox202 k).hi := by decide +kernel
private theorem accepted_202 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox202) tree202 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox202 midpoint_even_202
  simp only [tree202,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox202,candidate_valid h (FixedTape.midBox ibox202),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox202 101 (FixedTape.rowsAux denominator ibox202 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox202) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_202
private noncomputable def tree201 : TapeTree := .split 1 (((459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree202 tree203
attribute [irreducible] tree201
private theorem accepted_201 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox201) tree201 = true := by
  simp only [tree201,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox201 1 (459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 : Int) false,decode_split denominator ibox201 1 (459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_202 h,accepted_203 h⟩
private noncomputable def tree200 : TapeTree := .centered (candidateRows ibox200) (candidateRows (FixedTape.midBox ibox200))
attribute [irreducible] tree200
private theorem sign_200 : 2*denominator*(computed denominator (FixedTape.midBox ibox200)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox200).gradient k).lo.natAbs ((computed denominator ibox200).gradient k).hi.natAbs : Int)*((ibox200 k).hi-(ibox200 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox200
    (computed denominator ibox200) (computed denominator (FixedTape.midBox ibox200))
    (by decide +kernel)
private theorem midpoint_even_200 : ∀ k, 2 ∣ (ibox200 k).lo+(ibox200 k).hi := by decide +kernel
private theorem accepted_200 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox200) tree200 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox200 midpoint_even_200
  simp only [tree200,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox200,candidate_valid h (FixedTape.midBox ibox200),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox200 101 (FixedTape.rowsAux denominator ibox200 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox200) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_200
private noncomputable def tree199 : TapeTree := .centered (candidateRows ibox199) (candidateRows (FixedTape.midBox ibox199))
attribute [irreducible] tree199
private theorem sign_199 : 2*denominator*(computed denominator (FixedTape.midBox ibox199)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox199).gradient k).lo.natAbs ((computed denominator ibox199).gradient k).hi.natAbs : Int)*((ibox199 k).hi-(ibox199 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox199
    (computed denominator ibox199) (computed denominator (FixedTape.midBox ibox199))
    (by decide +kernel)
private theorem midpoint_even_199 : ∀ k, 2 ∣ (ibox199 k).lo+(ibox199 k).hi := by decide +kernel
private theorem accepted_199 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox199) tree199 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox199 midpoint_even_199
  simp only [tree199,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox199,candidate_valid h (FixedTape.midBox ibox199),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox199 101 (FixedTape.rowsAux denominator ibox199 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox199) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_199
private noncomputable def tree198 : TapeTree := .split 1 (((459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree199 tree200
attribute [irreducible] tree198
private theorem accepted_198 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox198) tree198 = true := by
  simp only [tree198,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox198 1 (459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 : Int) false,decode_split denominator ibox198 1 (459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_199 h,accepted_200 h⟩
private noncomputable def tree197 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree198 tree201
attribute [irreducible] tree197
private theorem accepted_197 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox197) tree197 = true := by
  simp only [tree197,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox197 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox197 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_198 h,accepted_201 h⟩
private noncomputable def tree196 : TapeTree := .split 1 (((486767162279429328739213547920690205360950627425221026413614394979123200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree197 tree204
attribute [irreducible] tree196
private theorem accepted_196 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox196) tree196 = true := by
  simp only [tree196,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox196 1 (486767162279429328739213547920690205360950627425221026413614394979123200000000000000000000000 : Int) false,decode_split denominator ibox196 1 (486767162279429328739213547920690205360950627425221026413614394979123200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_197 h,accepted_204 h⟩
private noncomputable def tree195 : TapeTree := .split 1 (((540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree196 tree211
attribute [irreducible] tree195
private theorem accepted_195 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox195) tree195 = true := by
  simp only [tree195,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox195 1 (540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 : Int) false,decode_split denominator ibox195 1 (540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_196 h,accepted_211 h⟩
private noncomputable def tree194 : TapeTree := .split 1 (((649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree195 tree232
attribute [irreducible] tree194
private theorem accepted_194 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox194) tree194 = true := by
  simp only [tree194,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox194 1 (649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 : Int) false,decode_split denominator ibox194 1 (649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_195 h,accepted_232 h⟩
private noncomputable def tree193 : TapeTree := .centered (candidateRows ibox193) (candidateRows (FixedTape.midBox ibox193))
attribute [irreducible] tree193
private theorem sign_193 : 2*denominator*(computed denominator (FixedTape.midBox ibox193)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox193).gradient k).lo.natAbs ((computed denominator ibox193).gradient k).hi.natAbs : Int)*((ibox193 k).hi-(ibox193 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox193
    (computed denominator ibox193) (computed denominator (FixedTape.midBox ibox193))
    (by decide +kernel)
private theorem midpoint_even_193 : ∀ k, 2 ∣ (ibox193 k).lo+(ibox193 k).hi := by decide +kernel
private theorem accepted_193 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox193) tree193 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox193 midpoint_even_193
  simp only [tree193,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox193,candidate_valid h (FixedTape.midBox ibox193),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox193 101 (FixedTape.rowsAux denominator ibox193 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox193) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_193
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
private noncomputable def tree191 : TapeTree := .split 1 (((405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree192 tree193
attribute [irreducible] tree191
private theorem accepted_191 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox191) tree191 = true := by
  simp only [tree191,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox191 1 (405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) false,decode_split denominator ibox191 1 (405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_192 h,accepted_193 h⟩
private noncomputable def tree190 : TapeTree := .centered (candidateRows ibox190) (candidateRows (FixedTape.midBox ibox190))
attribute [irreducible] tree190
private theorem sign_190 : 2*denominator*(computed denominator (FixedTape.midBox ibox190)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox190).gradient k).lo.natAbs ((computed denominator ibox190).gradient k).hi.natAbs : Int)*((ibox190 k).hi-(ibox190 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox190
    (computed denominator ibox190) (computed denominator (FixedTape.midBox ibox190))
    (by decide +kernel)
private theorem midpoint_even_190 : ∀ k, 2 ∣ (ibox190 k).lo+(ibox190 k).hi := by decide +kernel
private theorem accepted_190 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox190) tree190 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox190 midpoint_even_190
  simp only [tree190,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox190,candidate_valid h (FixedTape.midBox ibox190),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox190 101 (FixedTape.rowsAux denominator ibox190 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox190) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_190
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
private noncomputable def tree188 : TapeTree := .split 1 (((405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree189 tree190
attribute [irreducible] tree188
private theorem accepted_188 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox188) tree188 = true := by
  simp only [tree188,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox188 1 (405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) false,decode_split denominator ibox188 1 (405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_189 h,accepted_190 h⟩
private noncomputable def tree187 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree188 tree191
attribute [irreducible] tree187
private theorem accepted_187 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox187) tree187 = true := by
  simp only [tree187,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox187 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox187 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_188 h,accepted_191 h⟩
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
private noncomputable def tree185 : TapeTree := .centered (candidateRows ibox185) (candidateRows (FixedTape.midBox ibox185))
attribute [irreducible] tree185
private theorem sign_185 : 2*denominator*(computed denominator (FixedTape.midBox ibox185)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox185).gradient k).lo.natAbs ((computed denominator ibox185).gradient k).hi.natAbs : Int)*((ibox185 k).hi-(ibox185 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox185
    (computed denominator ibox185) (computed denominator (FixedTape.midBox ibox185))
    (by decide +kernel)
private theorem midpoint_even_185 : ∀ k, 2 ∣ (ibox185 k).lo+(ibox185 k).hi := by decide +kernel
private theorem accepted_185 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox185) tree185 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox185 midpoint_even_185
  simp only [tree185,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox185,candidate_valid h (FixedTape.midBox ibox185),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox185 101 (FixedTape.rowsAux denominator ibox185 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox185) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_185
private noncomputable def tree184 : TapeTree := .split 1 (((351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree185 tree186
attribute [irreducible] tree184
private theorem accepted_184 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox184) tree184 = true := by
  simp only [tree184,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox184 1 (351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) false,decode_split denominator ibox184 1 (351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_185 h,accepted_186 h⟩
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
private noncomputable def tree182 : TapeTree := .centered (candidateRows ibox182) (candidateRows (FixedTape.midBox ibox182))
attribute [irreducible] tree182
private theorem sign_182 : 2*denominator*(computed denominator (FixedTape.midBox ibox182)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox182).gradient k).lo.natAbs ((computed denominator ibox182).gradient k).hi.natAbs : Int)*((ibox182 k).hi-(ibox182 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox182
    (computed denominator ibox182) (computed denominator (FixedTape.midBox ibox182))
    (by decide +kernel)
private theorem midpoint_even_182 : ∀ k, 2 ∣ (ibox182 k).lo+(ibox182 k).hi := by decide +kernel
private theorem accepted_182 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox182) tree182 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox182 midpoint_even_182
  simp only [tree182,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox182,candidate_valid h (FixedTape.midBox ibox182),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox182 101 (FixedTape.rowsAux denominator ibox182 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox182) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_182
private noncomputable def tree181 : TapeTree := .split 1 (((351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree182 tree183
attribute [irreducible] tree181
private theorem accepted_181 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox181) tree181 = true := by
  simp only [tree181,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox181 1 (351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) false,decode_split denominator ibox181 1 (351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_182 h,accepted_183 h⟩
private noncomputable def tree180 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree181 tree184
attribute [irreducible] tree180
private theorem accepted_180 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox180) tree180 = true := by
  simp only [tree180,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox180 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox180 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_181 h,accepted_184 h⟩
private noncomputable def tree179 : TapeTree := .split 1 (((378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree180 tree187
attribute [irreducible] tree179
private theorem accepted_179 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox179) tree179 = true := by
  simp only [tree179,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox179 1 (378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 : Int) false,decode_split denominator ibox179 1 (378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_180 h,accepted_187 h⟩
private noncomputable def tree178 : TapeTree := .centered (candidateRows ibox178) (candidateRows (FixedTape.midBox ibox178))
attribute [irreducible] tree178
private theorem sign_178 : 2*denominator*(computed denominator (FixedTape.midBox ibox178)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox178).gradient k).lo.natAbs ((computed denominator ibox178).gradient k).hi.natAbs : Int)*((ibox178 k).hi-(ibox178 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox178
    (computed denominator ibox178) (computed denominator (FixedTape.midBox ibox178))
    (by decide +kernel)
private theorem midpoint_even_178 : ∀ k, 2 ∣ (ibox178 k).lo+(ibox178 k).hi := by decide +kernel
private theorem accepted_178 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox178) tree178 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox178 midpoint_even_178
  simp only [tree178,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox178,candidate_valid h (FixedTape.midBox ibox178),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox178 101 (FixedTape.rowsAux denominator ibox178 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox178) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_178
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
private noncomputable def tree176 : TapeTree := .split 1 (((297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree177 tree178
attribute [irreducible] tree176
private theorem accepted_176 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox176) tree176 = true := by
  simp only [tree176,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox176 1 (297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) false,decode_split denominator ibox176 1 (297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_177 h,accepted_178 h⟩
private noncomputable def tree175 : TapeTree := .centered (candidateRows ibox175) (candidateRows (FixedTape.midBox ibox175))
attribute [irreducible] tree175
private theorem sign_175 : 2*denominator*(computed denominator (FixedTape.midBox ibox175)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox175).gradient k).lo.natAbs ((computed denominator ibox175).gradient k).hi.natAbs : Int)*((ibox175 k).hi-(ibox175 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox175
    (computed denominator ibox175) (computed denominator (FixedTape.midBox ibox175))
    (by decide +kernel)
private theorem midpoint_even_175 : ∀ k, 2 ∣ (ibox175 k).lo+(ibox175 k).hi := by decide +kernel
private theorem accepted_175 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox175) tree175 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox175 midpoint_even_175
  simp only [tree175,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox175,candidate_valid h (FixedTape.midBox ibox175),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox175 101 (FixedTape.rowsAux denominator ibox175 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox175) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_175
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
private noncomputable def tree173 : TapeTree := .split 1 (((297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree174 tree175
attribute [irreducible] tree173
private theorem accepted_173 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox173) tree173 = true := by
  simp only [tree173,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox173 1 (297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) false,decode_split denominator ibox173 1 (297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_174 h,accepted_175 h⟩
private noncomputable def tree172 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree173 tree176
attribute [irreducible] tree172
private theorem accepted_172 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox172) tree172 = true := by
  simp only [tree172,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox172 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox172 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_173 h,accepted_176 h⟩
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
private noncomputable def tree170 : TapeTree := .centered (candidateRows ibox170) (candidateRows (FixedTape.midBox ibox170))
attribute [irreducible] tree170
private theorem sign_170 : 2*denominator*(computed denominator (FixedTape.midBox ibox170)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox170).gradient k).lo.natAbs ((computed denominator ibox170).gradient k).hi.natAbs : Int)*((ibox170 k).hi-(ibox170 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox170
    (computed denominator ibox170) (computed denominator (FixedTape.midBox ibox170))
    (by decide +kernel)
private theorem midpoint_even_170 : ∀ k, 2 ∣ (ibox170 k).lo+(ibox170 k).hi := by decide +kernel
private theorem accepted_170 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox170) tree170 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox170 midpoint_even_170
  simp only [tree170,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox170,candidate_valid h (FixedTape.midBox ibox170),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox170 101 (FixedTape.rowsAux denominator ibox170 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox170) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_170
private noncomputable def tree169 : TapeTree := .split 1 (((243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree170 tree171
attribute [irreducible] tree169
private theorem accepted_169 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox169) tree169 = true := by
  simp only [tree169,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox169 1 (243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) false,decode_split denominator ibox169 1 (243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_170 h,accepted_171 h⟩
private noncomputable def tree168 : TapeTree := .centered (candidateRows ibox168) (candidateRows (FixedTape.midBox ibox168))
attribute [irreducible] tree168
private theorem sign_168 : 2*denominator*(computed denominator (FixedTape.midBox ibox168)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox168).gradient k).lo.natAbs ((computed denominator ibox168).gradient k).hi.natAbs : Int)*((ibox168 k).hi-(ibox168 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox168
    (computed denominator ibox168) (computed denominator (FixedTape.midBox ibox168))
    (by decide +kernel)
private theorem midpoint_even_168 : ∀ k, 2 ∣ (ibox168 k).lo+(ibox168 k).hi := by decide +kernel
private theorem accepted_168 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox168) tree168 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox168 midpoint_even_168
  simp only [tree168,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox168,candidate_valid h (FixedTape.midBox ibox168),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox168 101 (FixedTape.rowsAux denominator ibox168 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox168) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_168
private noncomputable def tree167 : TapeTree := .centered (candidateRows ibox167) (candidateRows (FixedTape.midBox ibox167))
attribute [irreducible] tree167
private theorem sign_167 : 2*denominator*(computed denominator (FixedTape.midBox ibox167)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox167).gradient k).lo.natAbs ((computed denominator ibox167).gradient k).hi.natAbs : Int)*((ibox167 k).hi-(ibox167 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox167
    (computed denominator ibox167) (computed denominator (FixedTape.midBox ibox167))
    (by decide +kernel)
private theorem midpoint_even_167 : ∀ k, 2 ∣ (ibox167 k).lo+(ibox167 k).hi := by decide +kernel
private theorem accepted_167 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox167) tree167 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox167 midpoint_even_167
  simp only [tree167,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox167,candidate_valid h (FixedTape.midBox ibox167),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox167 101 (FixedTape.rowsAux denominator ibox167 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox167) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_167
private noncomputable def tree166 : TapeTree := .split 1 (((243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree167 tree168
attribute [irreducible] tree166
private theorem accepted_166 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox166) tree166 = true := by
  simp only [tree166,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox166 1 (243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) false,decode_split denominator ibox166 1 (243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_167 h,accepted_168 h⟩
private noncomputable def tree165 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree166 tree169
attribute [irreducible] tree165
private theorem accepted_165 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox165) tree165 = true := by
  simp only [tree165,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox165 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox165 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_166 h,accepted_169 h⟩
private noncomputable def tree164 : TapeTree := .split 1 (((270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree165 tree172
attribute [irreducible] tree164
private theorem accepted_164 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox164) tree164 = true := by
  simp only [tree164,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox164 1 (270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 : Int) false,decode_split denominator ibox164 1 (270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_165 h,accepted_172 h⟩
private noncomputable def tree163 : TapeTree := .split 1 (((324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree164 tree179
attribute [irreducible] tree163
private theorem accepted_163 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox163) tree163 = true := by
  simp only [tree163,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox163 1 (324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 : Int) false,decode_split denominator ibox163 1 (324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_164 h,accepted_179 h⟩
private noncomputable def tree162 : TapeTree := .centered (candidateRows ibox162) (candidateRows (FixedTape.midBox ibox162))
attribute [irreducible] tree162
private theorem sign_162 : 2*denominator*(computed denominator (FixedTape.midBox ibox162)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox162).gradient k).lo.natAbs ((computed denominator ibox162).gradient k).hi.natAbs : Int)*((ibox162 k).hi-(ibox162 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox162
    (computed denominator ibox162) (computed denominator (FixedTape.midBox ibox162))
    (by decide +kernel)
private theorem midpoint_even_162 : ∀ k, 2 ∣ (ibox162 k).lo+(ibox162 k).hi := by decide +kernel
private theorem accepted_162 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox162) tree162 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox162 midpoint_even_162
  simp only [tree162,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox162,candidate_valid h (FixedTape.midBox ibox162),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox162 101 (FixedTape.rowsAux denominator ibox162 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox162) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_162
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
private noncomputable def tree160 : TapeTree := .split 1 (((189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree161 tree162
attribute [irreducible] tree160
private theorem accepted_160 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox160) tree160 = true := by
  simp only [tree160,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox160 1 (189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) false,decode_split denominator ibox160 1 (189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_161 h,accepted_162 h⟩
private noncomputable def tree159 : TapeTree := .centered (candidateRows ibox159) (candidateRows (FixedTape.midBox ibox159))
attribute [irreducible] tree159
private theorem sign_159 : 2*denominator*(computed denominator (FixedTape.midBox ibox159)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox159).gradient k).lo.natAbs ((computed denominator ibox159).gradient k).hi.natAbs : Int)*((ibox159 k).hi-(ibox159 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox159
    (computed denominator ibox159) (computed denominator (FixedTape.midBox ibox159))
    (by decide +kernel)
private theorem midpoint_even_159 : ∀ k, 2 ∣ (ibox159 k).lo+(ibox159 k).hi := by decide +kernel
private theorem accepted_159 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox159) tree159 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox159 midpoint_even_159
  simp only [tree159,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox159,candidate_valid h (FixedTape.midBox ibox159),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox159 101 (FixedTape.rowsAux denominator ibox159 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox159) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_159
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
private noncomputable def tree157 : TapeTree := .split 1 (((189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree158 tree159
attribute [irreducible] tree157
private theorem accepted_157 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox157) tree157 = true := by
  simp only [tree157,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox157 1 (189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) false,decode_split denominator ibox157 1 (189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_158 h,accepted_159 h⟩
private noncomputable def tree156 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree157 tree160
attribute [irreducible] tree156
private theorem accepted_156 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox156) tree156 = true := by
  simp only [tree156,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox156 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox156 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_157 h,accepted_160 h⟩
private noncomputable def tree155 : TapeTree := .centered (candidateRows ibox155) (candidateRows (FixedTape.midBox ibox155))
attribute [irreducible] tree155
private theorem sign_155 : 2*denominator*(computed denominator (FixedTape.midBox ibox155)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox155).gradient k).lo.natAbs ((computed denominator ibox155).gradient k).hi.natAbs : Int)*((ibox155 k).hi-(ibox155 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox155
    (computed denominator ibox155) (computed denominator (FixedTape.midBox ibox155))
    (by decide +kernel)
private theorem midpoint_even_155 : ∀ k, 2 ∣ (ibox155 k).lo+(ibox155 k).hi := by decide +kernel
private theorem accepted_155 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox155) tree155 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox155 midpoint_even_155
  simp only [tree155,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox155,candidate_valid h (FixedTape.midBox ibox155),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox155 101 (FixedTape.rowsAux denominator ibox155 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox155) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_155
private noncomputable def tree154 : TapeTree := .centered (candidateRows ibox154) (candidateRows (FixedTape.midBox ibox154))
attribute [irreducible] tree154
private theorem sign_154 : 2*denominator*(computed denominator (FixedTape.midBox ibox154)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox154).gradient k).lo.natAbs ((computed denominator ibox154).gradient k).hi.natAbs : Int)*((ibox154 k).hi-(ibox154 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox154
    (computed denominator ibox154) (computed denominator (FixedTape.midBox ibox154))
    (by decide +kernel)
private theorem midpoint_even_154 : ∀ k, 2 ∣ (ibox154 k).lo+(ibox154 k).hi := by decide +kernel
private theorem accepted_154 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox154) tree154 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox154 midpoint_even_154
  simp only [tree154,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox154,candidate_valid h (FixedTape.midBox ibox154),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox154 101 (FixedTape.rowsAux denominator ibox154 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox154) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_154
private noncomputable def tree153 : TapeTree := .split 1 (((135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree154 tree155
attribute [irreducible] tree153
private theorem accepted_153 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox153) tree153 = true := by
  simp only [tree153,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox153 1 (135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) false,decode_split denominator ibox153 1 (135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_154 h,accepted_155 h⟩
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
private noncomputable def tree151 : TapeTree := .centered (candidateRows ibox151) (candidateRows (FixedTape.midBox ibox151))
attribute [irreducible] tree151
private theorem sign_151 : 2*denominator*(computed denominator (FixedTape.midBox ibox151)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox151).gradient k).lo.natAbs ((computed denominator ibox151).gradient k).hi.natAbs : Int)*((ibox151 k).hi-(ibox151 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox151
    (computed denominator ibox151) (computed denominator (FixedTape.midBox ibox151))
    (by decide +kernel)
private theorem midpoint_even_151 : ∀ k, 2 ∣ (ibox151 k).lo+(ibox151 k).hi := by decide +kernel
private theorem accepted_151 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox151) tree151 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox151 midpoint_even_151
  simp only [tree151,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox151,candidate_valid h (FixedTape.midBox ibox151),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox151 101 (FixedTape.rowsAux denominator ibox151 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox151) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_151
private noncomputable def tree150 : TapeTree := .split 1 (((135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree151 tree152
attribute [irreducible] tree150
private theorem accepted_150 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox150) tree150 = true := by
  simp only [tree150,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox150 1 (135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) false,decode_split denominator ibox150 1 (135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_151 h,accepted_152 h⟩
private noncomputable def tree149 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree150 tree153
attribute [irreducible] tree149
private theorem accepted_149 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox149) tree149 = true := by
  simp only [tree149,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox149 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox149 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_150 h,accepted_153 h⟩
private noncomputable def tree148 : TapeTree := .split 1 (((162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree149 tree156
attribute [irreducible] tree148
private theorem accepted_148 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox148) tree148 = true := by
  simp only [tree148,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox148 1 (162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 : Int) false,decode_split denominator ibox148 1 (162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_149 h,accepted_156 h⟩
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
private noncomputable def tree146 : TapeTree := .centered (candidateRows ibox146) (candidateRows (FixedTape.midBox ibox146))
attribute [irreducible] tree146
private theorem sign_146 : 2*denominator*(computed denominator (FixedTape.midBox ibox146)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox146).gradient k).lo.natAbs ((computed denominator ibox146).gradient k).hi.natAbs : Int)*((ibox146 k).hi-(ibox146 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox146
    (computed denominator ibox146) (computed denominator (FixedTape.midBox ibox146))
    (by decide +kernel)
private theorem midpoint_even_146 : ∀ k, 2 ∣ (ibox146 k).lo+(ibox146 k).hi := by decide +kernel
private theorem accepted_146 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox146) tree146 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox146 midpoint_even_146
  simp only [tree146,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox146,candidate_valid h (FixedTape.midBox ibox146),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox146 101 (FixedTape.rowsAux denominator ibox146 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox146) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_146
private noncomputable def tree145 : TapeTree := .split 1 (((81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree146 tree147
attribute [irreducible] tree145
private theorem accepted_145 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox145) tree145 = true := by
  simp only [tree145,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox145 1 (81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) false,decode_split denominator ibox145 1 (81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_146 h,accepted_147 h⟩
private noncomputable def tree144 : TapeTree := .centered (candidateRows ibox144) (candidateRows (FixedTape.midBox ibox144))
attribute [irreducible] tree144
private theorem sign_144 : 2*denominator*(computed denominator (FixedTape.midBox ibox144)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox144).gradient k).lo.natAbs ((computed denominator ibox144).gradient k).hi.natAbs : Int)*((ibox144 k).hi-(ibox144 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox144
    (computed denominator ibox144) (computed denominator (FixedTape.midBox ibox144))
    (by decide +kernel)
private theorem midpoint_even_144 : ∀ k, 2 ∣ (ibox144 k).lo+(ibox144 k).hi := by decide +kernel
private theorem accepted_144 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox144) tree144 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox144 midpoint_even_144
  simp only [tree144,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox144,candidate_valid h (FixedTape.midBox ibox144),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox144 101 (FixedTape.rowsAux denominator ibox144 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox144) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_144
private noncomputable def tree143 : TapeTree := .centered (candidateRows ibox143) (candidateRows (FixedTape.midBox ibox143))
attribute [irreducible] tree143
private theorem sign_143 : 2*denominator*(computed denominator (FixedTape.midBox ibox143)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox143).gradient k).lo.natAbs ((computed denominator ibox143).gradient k).hi.natAbs : Int)*((ibox143 k).hi-(ibox143 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox143
    (computed denominator ibox143) (computed denominator (FixedTape.midBox ibox143))
    (by decide +kernel)
private theorem midpoint_even_143 : ∀ k, 2 ∣ (ibox143 k).lo+(ibox143 k).hi := by decide +kernel
private theorem accepted_143 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox143) tree143 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox143 midpoint_even_143
  simp only [tree143,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox143,candidate_valid h (FixedTape.midBox ibox143),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox143 101 (FixedTape.rowsAux denominator ibox143 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox143) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_143
private noncomputable def tree142 : TapeTree := .split 1 (((81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree143 tree144
attribute [irreducible] tree142
private theorem accepted_142 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox142) tree142 = true := by
  simp only [tree142,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox142 1 (81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) false,decode_split denominator ibox142 1 (81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_143 h,accepted_144 h⟩
private noncomputable def tree141 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree142 tree145
attribute [irreducible] tree141
private theorem accepted_141 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox141) tree141 = true := by
  simp only [tree141,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox141 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox141 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_142 h,accepted_145 h⟩
private noncomputable def tree140 : TapeTree := .centered (candidateRows ibox140) (candidateRows (FixedTape.midBox ibox140))
attribute [irreducible] tree140
private theorem sign_140 : 2*denominator*(computed denominator (FixedTape.midBox ibox140)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox140).gradient k).lo.natAbs ((computed denominator ibox140).gradient k).hi.natAbs : Int)*((ibox140 k).hi-(ibox140 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox140
    (computed denominator ibox140) (computed denominator (FixedTape.midBox ibox140))
    (by decide +kernel)
private theorem midpoint_even_140 : ∀ k, 2 ∣ (ibox140 k).lo+(ibox140 k).hi := by decide +kernel
private theorem accepted_140 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox140) tree140 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox140 midpoint_even_140
  simp only [tree140,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox140,candidate_valid h (FixedTape.midBox ibox140),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox140 101 (FixedTape.rowsAux denominator ibox140 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox140) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_140
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
private noncomputable def tree138 : TapeTree := .split 1 (((27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree139 tree140
attribute [irreducible] tree138
private theorem accepted_138 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox138) tree138 = true := by
  simp only [tree138,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox138 1 (27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) false,decode_split denominator ibox138 1 (27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) true]
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
private noncomputable def tree135 : TapeTree := .split 1 (((27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree136 tree137
attribute [irreducible] tree135
private theorem accepted_135 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox135) tree135 = true := by
  simp only [tree135,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox135 1 (27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) false,decode_split denominator ibox135 1 (27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_136 h,accepted_137 h⟩
private noncomputable def tree134 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree135 tree138
attribute [irreducible] tree134
private theorem accepted_134 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox134) tree134 = true := by
  simp only [tree134,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox134 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox134 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_135 h,accepted_138 h⟩
private noncomputable def tree133 : TapeTree := .split 1 (((54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree134 tree141
attribute [irreducible] tree133
private theorem accepted_133 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox133) tree133 = true := by
  simp only [tree133,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox133 1 (54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 : Int) false,decode_split denominator ibox133 1 (54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_134 h,accepted_141 h⟩
private noncomputable def tree132 : TapeTree := .split 1 (((108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree133 tree148
attribute [irreducible] tree132
private theorem accepted_132 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox132) tree132 = true := by
  simp only [tree132,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox132 1 (108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 : Int) false,decode_split denominator ibox132 1 (108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_133 h,accepted_148 h⟩
private noncomputable def tree131 : TapeTree := .split 1 (((216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree132 tree163
attribute [irreducible] tree131
private theorem accepted_131 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox131) tree131 = true := by
  simp only [tree131,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox131 1 (216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 : Int) false,decode_split denominator ibox131 1 (216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_132 h,accepted_163 h⟩
private noncomputable def tree130 : TapeTree := .split 1 (((432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree131 tree194
attribute [irreducible] tree130
private theorem accepted_130 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox130) tree130 = true := by
  simp only [tree130,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox130 1 (432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 : Int) false,decode_split denominator ibox130 1 (432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_131 h,accepted_194 h⟩
private noncomputable def tree129 : TapeTree := .split 2 (((649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree130 tree263
attribute [irreducible] tree129
private theorem accepted_129 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox129) tree129 = true := by
  simp only [tree129,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox129 2 (649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 : Int) false,decode_split denominator ibox129 2 (649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_130 h,accepted_263 h⟩
private noncomputable def tree128 : TapeTree := .centered (candidateRows ibox128) (candidateRows (FixedTape.midBox ibox128))
attribute [irreducible] tree128
private theorem sign_128 : 2*denominator*(computed denominator (FixedTape.midBox ibox128)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox128).gradient k).lo.natAbs ((computed denominator ibox128).gradient k).hi.natAbs : Int)*((ibox128 k).hi-(ibox128 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox128
    (computed denominator ibox128) (computed denominator (FixedTape.midBox ibox128))
    (by decide +kernel)
private theorem midpoint_even_128 : ∀ k, 2 ∣ (ibox128 k).lo+(ibox128 k).hi := by decide +kernel
private theorem accepted_128 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox128) tree128 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox128 midpoint_even_128
  simp only [tree128,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox128,candidate_valid h (FixedTape.midBox ibox128),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox128 101 (FixedTape.rowsAux denominator ibox128 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox128) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_128
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
private noncomputable def tree126 : TapeTree := .split 1 (((851842533989001325293623708861207859381663597994136796223825191213465600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree127 tree128
attribute [irreducible] tree126
private theorem accepted_126 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox126) tree126 = true := by
  simp only [tree126,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox126 1 (851842533989001325293623708861207859381663597994136796223825191213465600000000000000000000000 : Int) false,decode_split denominator ibox126 1 (851842533989001325293623708861207859381663597994136796223825191213465600000000000000000000000 : Int) true]
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
private noncomputable def tree123 : TapeTree := .split 1 (((824799913862366362585889622865613959083833007581624516978624391492403200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree124 tree125
attribute [irreducible] tree123
private theorem accepted_123 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox123) tree123 = true := by
  simp only [tree123,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox123 1 (824799913862366362585889622865613959083833007581624516978624391492403200000000000000000000000 : Int) false,decode_split denominator ibox123 1 (824799913862366362585889622865613959083833007581624516978624391492403200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_124 h,accepted_125 h⟩
private noncomputable def tree122 : TapeTree := .split 1 (((838321223925683843939756665863410909232748302787880656601224791352934400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree123 tree126
attribute [irreducible] tree122
private theorem accepted_122 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox122) tree122 = true := by
  simp only [tree122,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox122 1 (838321223925683843939756665863410909232748302787880656601224791352934400000000000000000000000 : Int) false,decode_split denominator ibox122 1 (838321223925683843939756665863410909232748302787880656601224791352934400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_123 h,accepted_126 h⟩
private noncomputable def tree121 : TapeTree := .centered (candidateRows ibox121) (candidateRows (FixedTape.midBox ibox121))
attribute [irreducible] tree121
private theorem sign_121 : 2*denominator*(computed denominator (FixedTape.midBox ibox121)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox121).gradient k).lo.natAbs ((computed denominator ibox121).gradient k).hi.natAbs : Int)*((ibox121 k).hi-(ibox121 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox121
    (computed denominator ibox121) (computed denominator (FixedTape.midBox ibox121))
    (by decide +kernel)
private theorem midpoint_even_121 : ∀ k, 2 ∣ (ibox121 k).lo+(ibox121 k).hi := by decide +kernel
private theorem accepted_121 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox121) tree121 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox121 midpoint_even_121
  simp only [tree121,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox121,candidate_valid h (FixedTape.midBox ibox121),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox121 101 (FixedTape.rowsAux denominator ibox121 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox121) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_121
private noncomputable def tree120 : TapeTree := .centered (candidateRows ibox120) (candidateRows (FixedTape.midBox ibox120))
attribute [irreducible] tree120
private theorem sign_120 : 2*denominator*(computed denominator (FixedTape.midBox ibox120)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox120).gradient k).lo.natAbs ((computed denominator ibox120).gradient k).hi.natAbs : Int)*((ibox120 k).hi-(ibox120 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox120
    (computed denominator ibox120) (computed denominator (FixedTape.midBox ibox120))
    (by decide +kernel)
private theorem midpoint_even_120 : ∀ k, 2 ∣ (ibox120 k).lo+(ibox120 k).hi := by decide +kernel
private theorem accepted_120 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox120) tree120 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox120 midpoint_even_120
  simp only [tree120,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox120,candidate_valid h (FixedTape.midBox ibox120),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox120 101 (FixedTape.rowsAux denominator ibox120 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox120) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_120
private noncomputable def tree119 : TapeTree := .split 1 (((797757293735731399878155536870020058786002417169112237733423591771340800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree120 tree121
attribute [irreducible] tree119
private theorem accepted_119 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox119) tree119 = true := by
  simp only [tree119,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox119 1 (797757293735731399878155536870020058786002417169112237733423591771340800000000000000000000000 : Int) false,decode_split denominator ibox119 1 (797757293735731399878155536870020058786002417169112237733423591771340800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_120 h,accepted_121 h⟩
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
private noncomputable def tree117 : TapeTree := .centered (candidateRows ibox117) (candidateRows (FixedTape.midBox ibox117))
attribute [irreducible] tree117
private theorem sign_117 : 2*denominator*(computed denominator (FixedTape.midBox ibox117)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox117).gradient k).lo.natAbs ((computed denominator ibox117).gradient k).hi.natAbs : Int)*((ibox117 k).hi-(ibox117 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox117
    (computed denominator ibox117) (computed denominator (FixedTape.midBox ibox117))
    (by decide +kernel)
private theorem midpoint_even_117 : ∀ k, 2 ∣ (ibox117 k).lo+(ibox117 k).hi := by decide +kernel
private theorem accepted_117 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox117) tree117 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox117 midpoint_even_117
  simp only [tree117,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox117,candidate_valid h (FixedTape.midBox ibox117),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox117 101 (FixedTape.rowsAux denominator ibox117 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox117) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_117
private noncomputable def tree116 : TapeTree := .split 1 (((770714673609096437170421450874426158488171826756599958488222792050278400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree117 tree118
attribute [irreducible] tree116
private theorem accepted_116 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox116) tree116 = true := by
  simp only [tree116,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox116 1 (770714673609096437170421450874426158488171826756599958488222792050278400000000000000000000000 : Int) false,decode_split denominator ibox116 1 (770714673609096437170421450874426158488171826756599958488222792050278400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_117 h,accepted_118 h⟩
private noncomputable def tree115 : TapeTree := .split 1 (((784235983672413918524288493872223108637087121962856098110823191910809600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree116 tree119
attribute [irreducible] tree115
private theorem accepted_115 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox115) tree115 = true := by
  simp only [tree115,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox115 1 (784235983672413918524288493872223108637087121962856098110823191910809600000000000000000000000 : Int) false,decode_split denominator ibox115 1 (784235983672413918524288493872223108637087121962856098110823191910809600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_116 h,accepted_119 h⟩
private noncomputable def tree114 : TapeTree := .split 1 (((811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree115 tree122
attribute [irreducible] tree114
private theorem accepted_114 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox114) tree114 = true := by
  simp only [tree114,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox114 1 (811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 : Int) false,decode_split denominator ibox114 1 (811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_115 h,accepted_122 h⟩
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
private noncomputable def tree112 : TapeTree := .centered (candidateRows ibox112) (candidateRows (FixedTape.midBox ibox112))
attribute [irreducible] tree112
private theorem sign_112 : 2*denominator*(computed denominator (FixedTape.midBox ibox112)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox112).gradient k).lo.natAbs ((computed denominator ibox112).gradient k).hi.natAbs : Int)*((ibox112 k).hi-(ibox112 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox112
    (computed denominator ibox112) (computed denominator (FixedTape.midBox ibox112))
    (by decide +kernel)
private theorem midpoint_even_112 : ∀ k, 2 ∣ (ibox112 k).lo+(ibox112 k).hi := by decide +kernel
private theorem accepted_112 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox112) tree112 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox112 midpoint_even_112
  simp only [tree112,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox112,candidate_valid h (FixedTape.midBox ibox112),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox112 101 (FixedTape.rowsAux denominator ibox112 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox112) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_112
private noncomputable def tree111 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree112 tree113
attribute [irreducible] tree111
private theorem accepted_111 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox111) tree111 = true := by
  simp only [tree111,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox111 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox111 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_112 h,accepted_113 h⟩
private noncomputable def tree110 : TapeTree := .centered (candidateRows ibox110) (candidateRows (FixedTape.midBox ibox110))
attribute [irreducible] tree110
private theorem sign_110 : 2*denominator*(computed denominator (FixedTape.midBox ibox110)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox110).gradient k).lo.natAbs ((computed denominator ibox110).gradient k).hi.natAbs : Int)*((ibox110 k).hi-(ibox110 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox110
    (computed denominator ibox110) (computed denominator (FixedTape.midBox ibox110))
    (by decide +kernel)
private theorem midpoint_even_110 : ∀ k, 2 ∣ (ibox110 k).lo+(ibox110 k).hi := by decide +kernel
private theorem accepted_110 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox110) tree110 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox110 midpoint_even_110
  simp only [tree110,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox110,candidate_valid h (FixedTape.midBox ibox110),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox110 101 (FixedTape.rowsAux denominator ibox110 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox110) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_110
private noncomputable def tree109 : TapeTree := .centered (candidateRows ibox109) (candidateRows (FixedTape.midBox ibox109))
attribute [irreducible] tree109
private theorem sign_109 : 2*denominator*(computed denominator (FixedTape.midBox ibox109)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox109).gradient k).lo.natAbs ((computed denominator ibox109).gradient k).hi.natAbs : Int)*((ibox109 k).hi-(ibox109 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox109
    (computed denominator ibox109) (computed denominator (FixedTape.midBox ibox109))
    (by decide +kernel)
private theorem midpoint_even_109 : ∀ k, 2 ∣ (ibox109 k).lo+(ibox109 k).hi := by decide +kernel
private theorem accepted_109 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox109) tree109 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox109 midpoint_even_109
  simp only [tree109,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox109,candidate_valid h (FixedTape.midBox ibox109),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox109 101 (FixedTape.rowsAux denominator ibox109 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox109) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_109
private noncomputable def tree108 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree109 tree110
attribute [irreducible] tree108
private theorem accepted_108 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox108) tree108 = true := by
  simp only [tree108,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox108 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox108 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_109 h,accepted_110 h⟩
private noncomputable def tree107 : TapeTree := .split 1 (((730150743419143993108820321881035308041425941137831539620421592468684800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree108 tree111
attribute [irreducible] tree107
private theorem accepted_107 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox107) tree107 = true := by
  simp only [tree107,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox107 1 (730150743419143993108820321881035308041425941137831539620421592468684800000000000000000000000 : Int) false,decode_split denominator ibox107 1 (730150743419143993108820321881035308041425941137831539620421592468684800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_108 h,accepted_111 h⟩
private noncomputable def tree106 : TapeTree := .centered (candidateRows ibox106) (candidateRows (FixedTape.midBox ibox106))
attribute [irreducible] tree106
private theorem sign_106 : 2*denominator*(computed denominator (FixedTape.midBox ibox106)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox106).gradient k).lo.natAbs ((computed denominator ibox106).gradient k).hi.natAbs : Int)*((ibox106 k).hi-(ibox106 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox106
    (computed denominator ibox106) (computed denominator (FixedTape.midBox ibox106))
    (by decide +kernel)
private theorem midpoint_even_106 : ∀ k, 2 ∣ (ibox106 k).lo+(ibox106 k).hi := by decide +kernel
private theorem accepted_106 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox106) tree106 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox106 midpoint_even_106
  simp only [tree106,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox106,candidate_valid h (FixedTape.midBox ibox106),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox106 101 (FixedTape.rowsAux denominator ibox106 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox106) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_106
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
private noncomputable def tree104 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree105 tree106
attribute [irreducible] tree104
private theorem accepted_104 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox104) tree104 = true := by
  simp only [tree104,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox104 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox104 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_105 h,accepted_106 h⟩
private noncomputable def tree103 : TapeTree := .centered (candidateRows ibox103) (candidateRows (FixedTape.midBox ibox103))
attribute [irreducible] tree103
private theorem sign_103 : 2*denominator*(computed denominator (FixedTape.midBox ibox103)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox103).gradient k).lo.natAbs ((computed denominator ibox103).gradient k).hi.natAbs : Int)*((ibox103 k).hi-(ibox103 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox103
    (computed denominator ibox103) (computed denominator (FixedTape.midBox ibox103))
    (by decide +kernel)
private theorem midpoint_even_103 : ∀ k, 2 ∣ (ibox103 k).lo+(ibox103 k).hi := by decide +kernel
private theorem accepted_103 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox103) tree103 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox103 midpoint_even_103
  simp only [tree103,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox103,candidate_valid h (FixedTape.midBox ibox103),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox103 101 (FixedTape.rowsAux denominator ibox103 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox103) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_103
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
private noncomputable def tree101 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree102 tree103
attribute [irreducible] tree101
private theorem accepted_101 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox101) tree101 = true := by
  simp only [tree101,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox101 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox101 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_102 h,accepted_103 h⟩
private noncomputable def tree100 : TapeTree := .split 1 (((676065503165874067693352149889847507445764760312806981130019993026560000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree101 tree104
attribute [irreducible] tree100
private theorem accepted_100 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox100) tree100 = true := by
  simp only [tree100,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox100 1 (676065503165874067693352149889847507445764760312806981130019993026560000000000000000000000000 : Int) false,decode_split denominator ibox100 1 (676065503165874067693352149889847507445764760312806981130019993026560000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_101 h,accepted_104 h⟩
private noncomputable def tree99 : TapeTree := .split 1 (((703108123292509030401086235885441407743595350725319260375220792747622400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree100 tree107
attribute [irreducible] tree99
private theorem accepted_99 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox99) tree99 = true := by
  simp only [tree99,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox99 1 (703108123292509030401086235885441407743595350725319260375220792747622400000000000000000000000 : Int) false,decode_split denominator ibox99 1 (703108123292509030401086235885441407743595350725319260375220792747622400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_100 h,accepted_107 h⟩
private noncomputable def tree98 : TapeTree := .split 1 (((757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree99 tree114
attribute [irreducible] tree98
private theorem accepted_98 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox98) tree98 = true := by
  simp only [tree98,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox98 1 (757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 : Int) false,decode_split denominator ibox98 1 (757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_99 h,accepted_114 h⟩
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
private noncomputable def tree96 : TapeTree := .centered (candidateRows ibox96) (candidateRows (FixedTape.midBox ibox96))
attribute [irreducible] tree96
private theorem sign_96 : 2*denominator*(computed denominator (FixedTape.midBox ibox96)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox96).gradient k).lo.natAbs ((computed denominator ibox96).gradient k).hi.natAbs : Int)*((ibox96 k).hi-(ibox96 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox96
    (computed denominator ibox96) (computed denominator (FixedTape.midBox ibox96))
    (by decide +kernel)
private theorem midpoint_even_96 : ∀ k, 2 ∣ (ibox96 k).lo+(ibox96 k).hi := by decide +kernel
private theorem accepted_96 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox96) tree96 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox96 midpoint_even_96
  simp only [tree96,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox96,candidate_valid h (FixedTape.midBox ibox96),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox96 101 (FixedTape.rowsAux denominator ibox96 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox96) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_96
private noncomputable def tree95 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree96 tree97
attribute [irreducible] tree95
private theorem accepted_95 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox95) tree95 = true := by
  simp only [tree95,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox95 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox95 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_96 h,accepted_97 h⟩
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
private noncomputable def tree92 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree93 tree94
attribute [irreducible] tree92
private theorem accepted_92 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox92) tree92 = true := by
  simp only [tree92,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox92 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox92 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_93 h,accepted_94 h⟩
private noncomputable def tree91 : TapeTree := .split 1 (((621980262912604142277883977898659706850103579487782422639618393584435200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree92 tree95
attribute [irreducible] tree91
private theorem accepted_91 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox91) tree91 = true := by
  simp only [tree91,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox91 1 (621980262912604142277883977898659706850103579487782422639618393584435200000000000000000000000 : Int) false,decode_split denominator ibox91 1 (621980262912604142277883977898659706850103579487782422639618393584435200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_92 h,accepted_95 h⟩
private noncomputable def tree90 : TapeTree := .centered (candidateRows ibox90) (candidateRows (FixedTape.midBox ibox90))
attribute [irreducible] tree90
private theorem sign_90 : 2*denominator*(computed denominator (FixedTape.midBox ibox90)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox90).gradient k).lo.natAbs ((computed denominator ibox90).gradient k).hi.natAbs : Int)*((ibox90 k).hi-(ibox90 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox90
    (computed denominator ibox90) (computed denominator (FixedTape.midBox ibox90))
    (by decide +kernel)
private theorem midpoint_even_90 : ∀ k, 2 ∣ (ibox90 k).lo+(ibox90 k).hi := by decide +kernel
private theorem accepted_90 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox90) tree90 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox90 midpoint_even_90
  simp only [tree90,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox90,candidate_valid h (FixedTape.midBox ibox90),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox90 101 (FixedTape.rowsAux denominator ibox90 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox90) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_90
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
private noncomputable def tree88 : TapeTree := .split 1 (((567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree89 tree90
attribute [irreducible] tree88
private theorem accepted_88 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox88) tree88 = true := by
  simp only [tree88,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox88 1 (567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 : Int) false,decode_split denominator ibox88 1 (567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_89 h,accepted_90 h⟩
private noncomputable def tree87 : TapeTree := .centered (candidateRows ibox87) (candidateRows (FixedTape.midBox ibox87))
attribute [irreducible] tree87
private theorem sign_87 : 2*denominator*(computed denominator (FixedTape.midBox ibox87)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox87).gradient k).lo.natAbs ((computed denominator ibox87).gradient k).hi.natAbs : Int)*((ibox87 k).hi-(ibox87 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox87
    (computed denominator ibox87) (computed denominator (FixedTape.midBox ibox87))
    (by decide +kernel)
private theorem midpoint_even_87 : ∀ k, 2 ∣ (ibox87 k).lo+(ibox87 k).hi := by decide +kernel
private theorem accepted_87 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox87) tree87 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox87 midpoint_even_87
  simp only [tree87,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox87,candidate_valid h (FixedTape.midBox ibox87),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox87 101 (FixedTape.rowsAux denominator ibox87 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox87) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_87
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
private noncomputable def tree85 : TapeTree := .split 1 (((567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree86 tree87
attribute [irreducible] tree85
private theorem accepted_85 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox85) tree85 = true := by
  simp only [tree85,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox85 1 (567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 : Int) false,decode_split denominator ibox85 1 (567895022659334216862415805907471906254442398662757864149216794142310400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_86 h,accepted_87 h⟩
private noncomputable def tree84 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree85 tree88
attribute [irreducible] tree84
private theorem accepted_84 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox84) tree84 = true := by
  simp only [tree84,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox84 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox84 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_85 h,accepted_88 h⟩
private noncomputable def tree83 : TapeTree := .split 1 (((594937642785969179570149891903065806552272989075270143394417593863372800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree84 tree91
attribute [irreducible] tree83
private theorem accepted_83 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox83) tree83 = true := by
  simp only [tree83,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox83 1 (594937642785969179570149891903065806552272989075270143394417593863372800000000000000000000000 : Int) false,decode_split denominator ibox83 1 (594937642785969179570149891903065806552272989075270143394417593863372800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_84 h,accepted_91 h⟩
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
private noncomputable def tree80 : TapeTree := .split 1 (((513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree81 tree82
attribute [irreducible] tree80
private theorem accepted_80 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox80) tree80 = true := by
  simp only [tree80,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox80 1 (513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 : Int) false,decode_split denominator ibox80 1 (513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 : Int) true]
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
private noncomputable def tree78 : TapeTree := .centered (candidateRows ibox78) (candidateRows (FixedTape.midBox ibox78))
attribute [irreducible] tree78
private theorem sign_78 : 2*denominator*(computed denominator (FixedTape.midBox ibox78)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox78).gradient k).lo.natAbs ((computed denominator ibox78).gradient k).hi.natAbs : Int)*((ibox78 k).hi-(ibox78 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox78
    (computed denominator ibox78) (computed denominator (FixedTape.midBox ibox78))
    (by decide +kernel)
private theorem midpoint_even_78 : ∀ k, 2 ∣ (ibox78 k).lo+(ibox78 k).hi := by decide +kernel
private theorem accepted_78 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox78) tree78 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox78 midpoint_even_78
  simp only [tree78,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox78,candidate_valid h (FixedTape.midBox ibox78),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox78 101 (FixedTape.rowsAux denominator ibox78 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox78) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_78
private noncomputable def tree77 : TapeTree := .split 1 (((513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree78 tree79
attribute [irreducible] tree77
private theorem accepted_77 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox77) tree77 = true := by
  simp only [tree77,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox77 1 (513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 : Int) false,decode_split denominator ibox77 1 (513809782406064291446947633916284105658781217837733305658815194700185600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_78 h,accepted_79 h⟩
private noncomputable def tree76 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree77 tree80
attribute [irreducible] tree76
private theorem accepted_76 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox76) tree76 = true := by
  simp only [tree76,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox76 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox76 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_77 h,accepted_80 h⟩
private noncomputable def tree75 : TapeTree := .centered (candidateRows ibox75) (candidateRows (FixedTape.midBox ibox75))
attribute [irreducible] tree75
private theorem sign_75 : 2*denominator*(computed denominator (FixedTape.midBox ibox75)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox75).gradient k).lo.natAbs ((computed denominator ibox75).gradient k).hi.natAbs : Int)*((ibox75 k).hi-(ibox75 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox75
    (computed denominator ibox75) (computed denominator (FixedTape.midBox ibox75))
    (by decide +kernel)
private theorem midpoint_even_75 : ∀ k, 2 ∣ (ibox75 k).lo+(ibox75 k).hi := by decide +kernel
private theorem accepted_75 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox75) tree75 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox75 midpoint_even_75
  simp only [tree75,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox75,candidate_valid h (FixedTape.midBox ibox75),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox75 101 (FixedTape.rowsAux denominator ibox75 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox75) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_75
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
private noncomputable def tree73 : TapeTree := .split 1 (((459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree74 tree75
attribute [irreducible] tree73
private theorem accepted_73 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox73) tree73 = true := by
  simp only [tree73,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox73 1 (459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 : Int) false,decode_split denominator ibox73 1 (459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_74 h,accepted_75 h⟩
private noncomputable def tree72 : TapeTree := .centered (candidateRows ibox72) (candidateRows (FixedTape.midBox ibox72))
attribute [irreducible] tree72
private theorem sign_72 : 2*denominator*(computed denominator (FixedTape.midBox ibox72)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox72).gradient k).lo.natAbs ((computed denominator ibox72).gradient k).hi.natAbs : Int)*((ibox72 k).hi-(ibox72 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox72
    (computed denominator ibox72) (computed denominator (FixedTape.midBox ibox72))
    (by decide +kernel)
private theorem midpoint_even_72 : ∀ k, 2 ∣ (ibox72 k).lo+(ibox72 k).hi := by decide +kernel
private theorem accepted_72 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox72) tree72 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox72 midpoint_even_72
  simp only [tree72,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox72,candidate_valid h (FixedTape.midBox ibox72),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox72 101 (FixedTape.rowsAux denominator ibox72 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox72) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_72
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
private noncomputable def tree70 : TapeTree := .split 1 (((459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree71 tree72
attribute [irreducible] tree70
private theorem accepted_70 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox70) tree70 = true := by
  simp only [tree70,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox70 1 (459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 : Int) false,decode_split denominator ibox70 1 (459724542152794366031479461925096305063120037012708747168413595258060800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_71 h,accepted_72 h⟩
private noncomputable def tree69 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree70 tree73
attribute [irreducible] tree69
private theorem accepted_69 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox69) tree69 = true := by
  simp only [tree69,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox69 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox69 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_70 h,accepted_73 h⟩
private noncomputable def tree68 : TapeTree := .split 1 (((486767162279429328739213547920690205360950627425221026413614394979123200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree69 tree76
attribute [irreducible] tree68
private theorem accepted_68 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox68) tree68 = true := by
  simp only [tree68,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox68 1 (486767162279429328739213547920690205360950627425221026413614394979123200000000000000000000000 : Int) false,decode_split denominator ibox68 1 (486767162279429328739213547920690205360950627425221026413614394979123200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_69 h,accepted_76 h⟩
private noncomputable def tree67 : TapeTree := .split 1 (((540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree68 tree83
attribute [irreducible] tree67
private theorem accepted_67 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox67) tree67 = true := by
  simp only [tree67,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox67 1 (540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 : Int) false,decode_split denominator ibox67 1 (540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_68 h,accepted_83 h⟩
private noncomputable def tree66 : TapeTree := .split 1 (((649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree67 tree98
attribute [irreducible] tree66
private theorem accepted_66 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox66) tree66 = true := by
  simp only [tree66,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox66 1 (649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 : Int) false,decode_split denominator ibox66 1 (649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_67 h,accepted_98 h⟩
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
private noncomputable def tree64 : TapeTree := .centered (candidateRows ibox64) (candidateRows (FixedTape.midBox ibox64))
attribute [irreducible] tree64
private theorem sign_64 : 2*denominator*(computed denominator (FixedTape.midBox ibox64)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox64).gradient k).lo.natAbs ((computed denominator ibox64).gradient k).hi.natAbs : Int)*((ibox64 k).hi-(ibox64 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox64
    (computed denominator ibox64) (computed denominator (FixedTape.midBox ibox64))
    (by decide +kernel)
private theorem midpoint_even_64 : ∀ k, 2 ∣ (ibox64 k).lo+(ibox64 k).hi := by decide +kernel
private theorem accepted_64 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox64) tree64 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox64 midpoint_even_64
  simp only [tree64,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox64,candidate_valid h (FixedTape.midBox ibox64),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox64 101 (FixedTape.rowsAux denominator ibox64 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox64) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_64
private noncomputable def tree63 : TapeTree := .split 1 (((405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree64 tree65
attribute [irreducible] tree63
private theorem accepted_63 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox63) tree63 = true := by
  simp only [tree63,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox63 1 (405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) false,decode_split denominator ibox63 1 (405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_64 h,accepted_65 h⟩
private noncomputable def tree62 : TapeTree := .centered (candidateRows ibox62) (candidateRows (FixedTape.midBox ibox62))
attribute [irreducible] tree62
private theorem sign_62 : 2*denominator*(computed denominator (FixedTape.midBox ibox62)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox62).gradient k).lo.natAbs ((computed denominator ibox62).gradient k).hi.natAbs : Int)*((ibox62 k).hi-(ibox62 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox62
    (computed denominator ibox62) (computed denominator (FixedTape.midBox ibox62))
    (by decide +kernel)
private theorem midpoint_even_62 : ∀ k, 2 ∣ (ibox62 k).lo+(ibox62 k).hi := by decide +kernel
private theorem accepted_62 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox62) tree62 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox62 midpoint_even_62
  simp only [tree62,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox62,candidate_valid h (FixedTape.midBox ibox62),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox62 101 (FixedTape.rowsAux denominator ibox62 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox62) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_62
private noncomputable def tree61 : TapeTree := .centered (candidateRows ibox61) (candidateRows (FixedTape.midBox ibox61))
attribute [irreducible] tree61
private theorem sign_61 : 2*denominator*(computed denominator (FixedTape.midBox ibox61)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox61).gradient k).lo.natAbs ((computed denominator ibox61).gradient k).hi.natAbs : Int)*((ibox61 k).hi-(ibox61 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox61
    (computed denominator ibox61) (computed denominator (FixedTape.midBox ibox61))
    (by decide +kernel)
private theorem midpoint_even_61 : ∀ k, 2 ∣ (ibox61 k).lo+(ibox61 k).hi := by decide +kernel
private theorem accepted_61 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox61) tree61 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox61 midpoint_even_61
  simp only [tree61,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox61,candidate_valid h (FixedTape.midBox ibox61),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox61 101 (FixedTape.rowsAux denominator ibox61 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox61) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_61
private noncomputable def tree60 : TapeTree := .split 1 (((405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree61 tree62
attribute [irreducible] tree60
private theorem accepted_60 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox60) tree60 = true := by
  simp only [tree60,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox60 1 (405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) false,decode_split denominator ibox60 1 (405639301899524440616011289933908504467458856187684188678011995815936000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_61 h,accepted_62 h⟩
private noncomputable def tree59 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree60 tree63
attribute [irreducible] tree59
private theorem accepted_59 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox59) tree59 = true := by
  simp only [tree59,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox59 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox59 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_60 h,accepted_63 h⟩
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
private noncomputable def tree56 : TapeTree := .split 1 (((351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree57 tree58
attribute [irreducible] tree56
private theorem accepted_56 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox56) tree56 = true := by
  simp only [tree56,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox56 1 (351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) false,decode_split denominator ibox56 1 (351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) true]
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
private noncomputable def tree54 : TapeTree := .centered (candidateRows ibox54) (candidateRows (FixedTape.midBox ibox54))
attribute [irreducible] tree54
private theorem sign_54 : 2*denominator*(computed denominator (FixedTape.midBox ibox54)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox54).gradient k).lo.natAbs ((computed denominator ibox54).gradient k).hi.natAbs : Int)*((ibox54 k).hi-(ibox54 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox54
    (computed denominator ibox54) (computed denominator (FixedTape.midBox ibox54))
    (by decide +kernel)
private theorem midpoint_even_54 : ∀ k, 2 ∣ (ibox54 k).lo+(ibox54 k).hi := by decide +kernel
private theorem accepted_54 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox54) tree54 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox54 midpoint_even_54
  simp only [tree54,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox54,candidate_valid h (FixedTape.midBox ibox54),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox54 101 (FixedTape.rowsAux denominator ibox54 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox54) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_54
private noncomputable def tree53 : TapeTree := .split 1 (((351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree54 tree55
attribute [irreducible] tree53
private theorem accepted_53 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox53) tree53 = true := by
  simp only [tree53,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox53 1 (351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) false,decode_split denominator ibox53 1 (351554061646254515200543117942720703871797675362659630187610396373811200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_54 h,accepted_55 h⟩
private noncomputable def tree52 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree53 tree56
attribute [irreducible] tree52
private theorem accepted_52 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox52) tree52 = true := by
  simp only [tree52,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox52 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox52 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_53 h,accepted_56 h⟩
private noncomputable def tree51 : TapeTree := .split 1 (((378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree52 tree59
attribute [irreducible] tree51
private theorem accepted_51 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox51) tree51 = true := by
  simp only [tree51,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox51 1 (378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 : Int) false,decode_split denominator ibox51 1 (378596681772889477908277203938314604169628265775171909432811196094873600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_52 h,accepted_59 h⟩
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
private noncomputable def tree49 : TapeTree := .centered (candidateRows ibox49) (candidateRows (FixedTape.midBox ibox49))
attribute [irreducible] tree49
private theorem sign_49 : 2*denominator*(computed denominator (FixedTape.midBox ibox49)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox49).gradient k).lo.natAbs ((computed denominator ibox49).gradient k).hi.natAbs : Int)*((ibox49 k).hi-(ibox49 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox49
    (computed denominator ibox49) (computed denominator (FixedTape.midBox ibox49))
    (by decide +kernel)
private theorem midpoint_even_49 : ∀ k, 2 ∣ (ibox49 k).lo+(ibox49 k).hi := by decide +kernel
private theorem accepted_49 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox49) tree49 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox49 midpoint_even_49
  simp only [tree49,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox49,candidate_valid h (FixedTape.midBox ibox49),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox49 101 (FixedTape.rowsAux denominator ibox49 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox49) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_49
private noncomputable def tree48 : TapeTree := .split 1 (((297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree49 tree50
attribute [irreducible] tree48
private theorem accepted_48 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox48) tree48 = true := by
  simp only [tree48,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox48 1 (297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) false,decode_split denominator ibox48 1 (297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_49 h,accepted_50 h⟩
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
private noncomputable def tree45 : TapeTree := .split 1 (((297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree46 tree47
attribute [irreducible] tree45
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox45 1 (297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) false,decode_split denominator ibox45 1 (297468821392984589785074945951532903276136494537635071697208796931686400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_46 h,accepted_47 h⟩
private noncomputable def tree44 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree45 tree48
attribute [irreducible] tree44
private theorem accepted_44 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox44) tree44 = true := by
  simp only [tree44,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox44 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox44 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_45 h,accepted_48 h⟩
private noncomputable def tree43 : TapeTree := .centered (candidateRows ibox43) (candidateRows (FixedTape.midBox ibox43))
attribute [irreducible] tree43
private theorem sign_43 : 2*denominator*(computed denominator (FixedTape.midBox ibox43)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox43).gradient k).lo.natAbs ((computed denominator ibox43).gradient k).hi.natAbs : Int)*((ibox43 k).hi-(ibox43 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox43
    (computed denominator ibox43) (computed denominator (FixedTape.midBox ibox43))
    (by decide +kernel)
private theorem midpoint_even_43 : ∀ k, 2 ∣ (ibox43 k).lo+(ibox43 k).hi := by decide +kernel
private theorem accepted_43 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox43) tree43 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox43 midpoint_even_43
  simp only [tree43,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox43,candidate_valid h (FixedTape.midBox ibox43),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox43 101 (FixedTape.rowsAux denominator ibox43 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox43) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_43
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
private noncomputable def tree41 : TapeTree := .split 1 (((243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree42 tree43
attribute [irreducible] tree41
private theorem accepted_41 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox41) tree41 = true := by
  simp only [tree41,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox41 1 (243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) false,decode_split denominator ibox41 1 (243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_42 h,accepted_43 h⟩
private noncomputable def tree40 : TapeTree := .centered (candidateRows ibox40) (candidateRows (FixedTape.midBox ibox40))
attribute [irreducible] tree40
private theorem sign_40 : 2*denominator*(computed denominator (FixedTape.midBox ibox40)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox40).gradient k).lo.natAbs ((computed denominator ibox40).gradient k).hi.natAbs : Int)*((ibox40 k).hi-(ibox40 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox40
    (computed denominator ibox40) (computed denominator (FixedTape.midBox ibox40))
    (by decide +kernel)
private theorem midpoint_even_40 : ∀ k, 2 ∣ (ibox40 k).lo+(ibox40 k).hi := by decide +kernel
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox40 midpoint_even_40
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox40,candidate_valid h (FixedTape.midBox ibox40),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox40 101 (FixedTape.rowsAux denominator ibox40 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox40) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_40
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
private noncomputable def tree38 : TapeTree := .split 1 (((243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree39 tree40
attribute [irreducible] tree38
private theorem accepted_38 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox38) tree38 = true := by
  simp only [tree38,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox38 1 (243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) false,decode_split denominator ibox38 1 (243383581139714664369606773960345102680475313712610513206807197489561600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_39 h,accepted_40 h⟩
private noncomputable def tree37 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree38 tree41
attribute [irreducible] tree37
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox37 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox37 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_38 h,accepted_41 h⟩
private noncomputable def tree36 : TapeTree := .split 1 (((270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree37 tree44
attribute [irreducible] tree36
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox36 1 (270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 : Int) false,decode_split denominator ibox36 1 (270426201266349627077340859955939002978305904125122792452007997210624000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_37 h,accepted_44 h⟩
private noncomputable def tree35 : TapeTree := .split 1 (((324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree36 tree51
attribute [irreducible] tree35
private theorem accepted_35 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox35) tree35 = true := by
  simp only [tree35,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox35 1 (324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 : Int) false,decode_split denominator ibox35 1 (324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_36 h,accepted_51 h⟩
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
private noncomputable def tree33 : TapeTree := .centered (candidateRows ibox33) (candidateRows (FixedTape.midBox ibox33))
attribute [irreducible] tree33
private theorem sign_33 : 2*denominator*(computed denominator (FixedTape.midBox ibox33)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox33).gradient k).lo.natAbs ((computed denominator ibox33).gradient k).hi.natAbs : Int)*((ibox33 k).hi-(ibox33 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox33
    (computed denominator ibox33) (computed denominator (FixedTape.midBox ibox33))
    (by decide +kernel)
private theorem midpoint_even_33 : ∀ k, 2 ∣ (ibox33 k).lo+(ibox33 k).hi := by decide +kernel
private theorem accepted_33 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox33) tree33 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox33 midpoint_even_33
  simp only [tree33,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox33,candidate_valid h (FixedTape.midBox ibox33),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox33 101 (FixedTape.rowsAux denominator ibox33 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox33) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_33
private noncomputable def tree32 : TapeTree := .split 1 (((189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree33 tree34
attribute [irreducible] tree32
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox32 1 (189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) false,decode_split denominator ibox32 1 (189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_33 h,accepted_34 h⟩
private noncomputable def tree31 : TapeTree := .centered (candidateRows ibox31) (candidateRows (FixedTape.midBox ibox31))
attribute [irreducible] tree31
private theorem sign_31 : 2*denominator*(computed denominator (FixedTape.midBox ibox31)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox31).gradient k).lo.natAbs ((computed denominator ibox31).gradient k).hi.natAbs : Int)*((ibox31 k).hi-(ibox31 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox31
    (computed denominator ibox31) (computed denominator (FixedTape.midBox ibox31))
    (by decide +kernel)
private theorem midpoint_even_31 : ∀ k, 2 ∣ (ibox31 k).lo+(ibox31 k).hi := by decide +kernel
private theorem accepted_31 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox31) tree31 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox31 midpoint_even_31
  simp only [tree31,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox31,candidate_valid h (FixedTape.midBox ibox31),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox31 101 (FixedTape.rowsAux denominator ibox31 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox31) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_31
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
private noncomputable def tree29 : TapeTree := .split 1 (((189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree30 tree31
attribute [irreducible] tree29
private theorem accepted_29 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox29) tree29 = true := by
  simp only [tree29,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox29 1 (189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) false,decode_split denominator ibox29 1 (189298340886444738954138601969157302084814132887585954716405598047436800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_30 h,accepted_31 h⟩
private noncomputable def tree28 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree29 tree32
attribute [irreducible] tree28
private theorem accepted_28 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox28) tree28 = true := by
  simp only [tree28,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox28 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox28 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_29 h,accepted_32 h⟩
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
private noncomputable def tree26 : TapeTree := .centered (candidateRows ibox26) (candidateRows (FixedTape.midBox ibox26))
attribute [irreducible] tree26
private theorem sign_26 : 2*denominator*(computed denominator (FixedTape.midBox ibox26)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox26).gradient k).lo.natAbs ((computed denominator ibox26).gradient k).hi.natAbs : Int)*((ibox26 k).hi-(ibox26 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox26
    (computed denominator ibox26) (computed denominator (FixedTape.midBox ibox26))
    (by decide +kernel)
private theorem midpoint_even_26 : ∀ k, 2 ∣ (ibox26 k).lo+(ibox26 k).hi := by decide +kernel
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox26 midpoint_even_26
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox26,candidate_valid h (FixedTape.midBox ibox26),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox26 101 (FixedTape.rowsAux denominator ibox26 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox26) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_26
private noncomputable def tree25 : TapeTree := .split 1 (((135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree26 tree27
attribute [irreducible] tree25
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox25 1 (135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) false,decode_split denominator ibox25 1 (135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_26 h,accepted_27 h⟩
private noncomputable def tree24 : TapeTree := .centered (candidateRows ibox24) (candidateRows (FixedTape.midBox ibox24))
attribute [irreducible] tree24
private theorem sign_24 : 2*denominator*(computed denominator (FixedTape.midBox ibox24)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox24).gradient k).lo.natAbs ((computed denominator ibox24).gradient k).hi.natAbs : Int)*((ibox24 k).hi-(ibox24 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox24
    (computed denominator ibox24) (computed denominator (FixedTape.midBox ibox24))
    (by decide +kernel)
private theorem midpoint_even_24 : ∀ k, 2 ∣ (ibox24 k).lo+(ibox24 k).hi := by decide +kernel
private theorem accepted_24 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox24) tree24 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox24 midpoint_even_24
  simp only [tree24,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox24,candidate_valid h (FixedTape.midBox ibox24),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox24 101 (FixedTape.rowsAux denominator ibox24 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox24) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_24
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
private noncomputable def tree22 : TapeTree := .split 1 (((135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree23 tree24
attribute [irreducible] tree22
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox22 1 (135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) false,decode_split denominator ibox22 1 (135213100633174813538670429977969501489152952062561396226003998605312000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_23 h,accepted_24 h⟩
private noncomputable def tree21 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree22 tree25
attribute [irreducible] tree21
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox21 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox21 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_22 h,accepted_25 h⟩
private noncomputable def tree20 : TapeTree := .split 1 (((162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree21 tree28
attribute [irreducible] tree20
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox20 1 (162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 : Int) false,decode_split denominator ibox20 1 (162255720759809776246404515973563401786983542475073675471204798326374400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_21 h,accepted_28 h⟩
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
private noncomputable def tree18 : TapeTree := .centered (candidateRows ibox18) (candidateRows (FixedTape.midBox ibox18))
attribute [irreducible] tree18
private theorem sign_18 : 2*denominator*(computed denominator (FixedTape.midBox ibox18)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox18).gradient k).lo.natAbs ((computed denominator ibox18).gradient k).hi.natAbs : Int)*((ibox18 k).hi-(ibox18 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox18
    (computed denominator ibox18) (computed denominator (FixedTape.midBox ibox18))
    (by decide +kernel)
private theorem midpoint_even_18 : ∀ k, 2 ∣ (ibox18 k).lo+(ibox18 k).hi := by decide +kernel
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox18 midpoint_even_18
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox18,candidate_valid h (FixedTape.midBox ibox18),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox18 101 (FixedTape.rowsAux denominator ibox18 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox18) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_18
private noncomputable def tree17 : TapeTree := .split 1 (((81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree18 tree19
attribute [irreducible] tree17
private theorem accepted_17 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox17) tree17 = true := by
  simp only [tree17,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox17 1 (81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) false,decode_split denominator ibox17 1 (81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_18 h,accepted_19 h⟩
private noncomputable def tree16 : TapeTree := .centered (candidateRows ibox16) (candidateRows (FixedTape.midBox ibox16))
attribute [irreducible] tree16
private theorem sign_16 : 2*denominator*(computed denominator (FixedTape.midBox ibox16)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox16).gradient k).lo.natAbs ((computed denominator ibox16).gradient k).hi.natAbs : Int)*((ibox16 k).hi-(ibox16 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox16
    (computed denominator ibox16) (computed denominator (FixedTape.midBox ibox16))
    (by decide +kernel)
private theorem midpoint_even_16 : ∀ k, 2 ∣ (ibox16 k).lo+(ibox16 k).hi := by decide +kernel
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox16 midpoint_even_16
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox16,candidate_valid h (FixedTape.midBox ibox16),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox16 101 (FixedTape.rowsAux denominator ibox16 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox16) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_16
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
private noncomputable def tree14 : TapeTree := .split 1 (((81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree15 tree16
attribute [irreducible] tree14
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox14 1 (81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) false,decode_split denominator ibox14 1 (81127860379904888123202257986781700893491771237536837735602399163187200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_15 h,accepted_16 h⟩
private noncomputable def tree13 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree14 tree17
attribute [irreducible] tree13
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox13 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox13 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_14 h,accepted_17 h⟩
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
private noncomputable def tree11 : TapeTree := .centered (candidateRows ibox11) (candidateRows (FixedTape.midBox ibox11))
attribute [irreducible] tree11
private theorem sign_11 : 2*denominator*(computed denominator (FixedTape.midBox ibox11)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox11).gradient k).lo.natAbs ((computed denominator ibox11).gradient k).hi.natAbs : Int)*((ibox11 k).hi-(ibox11 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox11
    (computed denominator ibox11) (computed denominator (FixedTape.midBox ibox11))
    (by decide +kernel)
private theorem midpoint_even_11 : ∀ k, 2 ∣ (ibox11 k).lo+(ibox11 k).hi := by decide +kernel
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox11 midpoint_even_11
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox11,candidate_valid h (FixedTape.midBox ibox11),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox11 101 (FixedTape.rowsAux denominator ibox11 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox11) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_11
private noncomputable def tree10 : TapeTree := .split 1 (((27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree11 tree12
attribute [irreducible] tree10
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox10 1 (27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) false,decode_split denominator ibox10 1 (27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_11 h,accepted_12 h⟩
private noncomputable def tree9 : TapeTree := .centered (candidateRows ibox9) (candidateRows (FixedTape.midBox ibox9))
attribute [irreducible] tree9
private theorem sign_9 : 2*denominator*(computed denominator (FixedTape.midBox ibox9)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox9).gradient k).lo.natAbs ((computed denominator ibox9).gradient k).hi.natAbs : Int)*((ibox9 k).hi-(ibox9 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox9
    (computed denominator ibox9) (computed denominator (FixedTape.midBox ibox9))
    (by decide +kernel)
private theorem midpoint_even_9 : ∀ k, 2 ∣ (ibox9 k).lo+(ibox9 k).hi := by decide +kernel
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox9 midpoint_even_9
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox9,candidate_valid h (FixedTape.midBox ibox9),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox9 101 (FixedTape.rowsAux denominator ibox9 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox9) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_9
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
private noncomputable def tree7 : TapeTree := .split 1 (((27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree8 tree9
attribute [irreducible] tree7
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox7 1 (27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) false,decode_split denominator ibox7 1 (27042620126634962707734085995593900297830590412512279245200799721062400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_8 h,accepted_9 h⟩
private noncomputable def tree6 : TapeTree := .split 0 (((833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree10
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) false,decode_split denominator ibox6 0 (833814120571244712333929119941438814099468266352622261079654431412521861547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_7 h,accepted_10 h⟩
private noncomputable def tree5 : TapeTree := .split 1 (((54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree6 tree13
attribute [irreducible] tree5
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox5 1 (54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 : Int) false,decode_split denominator ibox5 1 (54085240253269925415468171991187800595661180825024558490401599442124800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_6 h,accepted_13 h⟩
private noncomputable def tree4 : TapeTree := .split 1 (((108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree20
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 1 (108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 : Int) false,decode_split denominator ibox4 1 (108170480506539850830936343982375601191322361650049116980803198884249600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_20 h⟩
private noncomputable def tree3 : TapeTree := .split 1 (((216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree35
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 : Int) false,decode_split denominator ibox3 1 (216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_35 h⟩
private noncomputable def tree2 : TapeTree := .split 1 (((432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree66
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 1 (432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 : Int) false,decode_split denominator ibox2 1 (432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_66 h⟩
private noncomputable def tree1 : TapeTree := .split 2 (((432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree2 tree129
attribute [irreducible] tree1
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox1 2 (432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 : Int) false,decode_split denominator ibox1 2 (432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_2 h,accepted_129 h⟩
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
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (4791666666666667/5000000000000000 : ℚ) (31/32 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 101 = e104 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (4791666666666667/5000000000000000 : ℚ) (31/32 : ℚ)) x → eval e104 x ≤ 0 := by
  have hb := h.child_4 tape 101 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell123_high_first_top

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell123_high_first_top
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((4791666666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((31/32 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 123 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 123 p)
    (hkb : ((31/32 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((4791666666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : bStar < a), firstResidual (0 : Fin 9) a p r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell123_high_first_top.cell_bound h.child_8 h.child_9 (Cell123_high_first_top.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell123_high_first_top
