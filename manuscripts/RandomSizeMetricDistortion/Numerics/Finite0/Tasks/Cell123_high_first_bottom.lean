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
namespace Cell123_high_first_bottom
private noncomputable def qValues : Fin 2 → ℚ := ![(15562059649518128248733312094092471/5010122273867260946776040999324726025 : ℚ),(290893323061380864622400000000000000/200404890954690437871041639972989041 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics30.e2 qValues
private noncomputable abbrev e7 : PolyExpr := SharedFiniteSemantics30.e7 qValues
private noncomputable abbrev e11 : PolyExpr := SharedFiniteSemantics30.e11 qValues
private noncomputable abbrev e15 : PolyExpr := SharedFiniteSemantics30.e15 qValues
private noncomputable abbrev e88 : PolyExpr := SharedFiniteSemantics30.e88 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics30.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics30.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics30.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics30.node_4 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics30.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics30.node_7 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics30.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics30.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics30.node_11 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics30.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics30.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics30.node_15 qValues
private noncomputable abbrev node_53 := SharedFiniteSemantics30.node_53 qValues
private noncomputable abbrev node_54 := SharedFiniteSemantics30.node_54 qValues
private noncomputable abbrev node_55 := SharedFiniteSemantics30.node_55 qValues
private noncomputable abbrev node_56 := SharedFiniteSemantics30.node_56 qValues
private noncomputable abbrev node_57 := SharedFiniteSemantics30.node_57 qValues
private noncomputable abbrev node_58 := SharedFiniteSemantics30.node_58 qValues
private noncomputable abbrev node_59 := SharedFiniteSemantics30.node_59 qValues
private noncomputable abbrev node_60 := SharedFiniteSemantics30.node_60 qValues
private noncomputable abbrev node_62 := SharedFiniteSemantics30.node_62 qValues
private noncomputable abbrev node_63 := SharedFiniteSemantics30.node_63 qValues
private noncomputable abbrev node_64 := SharedFiniteSemantics30.node_64 qValues
private noncomputable abbrev node_65 := SharedFiniteSemantics30.node_65 qValues
private noncomputable abbrev node_66 := SharedFiniteSemantics30.node_66 qValues
private noncomputable abbrev node_67 := SharedFiniteSemantics30.node_67 qValues
private noncomputable abbrev node_68 := SharedFiniteSemantics30.node_68 qValues
private noncomputable abbrev node_69 := SharedFiniteSemantics30.node_69 qValues
private noncomputable abbrev node_70 := SharedFiniteSemantics30.node_70 qValues
private noncomputable abbrev node_87 := SharedFiniteSemantics30.node_87 qValues
private noncomputable abbrev node_88 := SharedFiniteSemantics30.node_88 qValues
private noncomputable abbrev semantic_H_36 := SharedFiniteSemantics30.semantic_H_36 qValues
private noncomputable abbrev semantic_H_52 := SharedFiniteSemantics30.semantic_H_52 qValues
private noncomputable abbrev semantic_psi_86 := SharedFiniteSemantics30.semantic_psi_86 qValues
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
    (1)*eval e88 x = (x 0*(1-x 0))*(aPoint x+priceLambda 123 (x 0)*(HStar (yPoint x)-HStar (aPoint x))+priceTau 123 (x 0)*psiStar (rPoint x)+(0)-(cStar)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_13,node_14,node_53,node_54,node_55,node_56,node_57,node_58,node_59,node_60,node_62,node_63,node_64,node_65,node_66,node_67,node_68,node_69,node_70,node_87,node_88,semantic_H_36,semantic_H_52,semantic_psi_86,point_7,point_11,point_2,point_15]
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
    (hL : lambdaStar (x 0) = priceLambda 123 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 123 (x 0)) :
    (1)*eval e88 x = (x 0*(1-x 0))*(firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (4791666666666667/5000000000000000 : ℚ) (31/32 : ℚ)) x → eval e88 x ≤ 0)
    (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((4791666666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((31/32 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 123 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 123 p)
    (hkb : ((31/32 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((4791666666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ bStar) :
    firstResidual (0 : Fin 9) a p r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨x,hx,hxp,hxa,hxr⟩ := h4 (4791666666666667/5000000000000000 : ℚ) (31/32 : ℚ) bStar p a r hpcell hkb hr ha hap hcase
  have hcut : ¬(((31/32 : ℚ) : ℝ) ≤ bStar) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,if_neg hcut] using hxa
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,if_neg hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 123 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 123 (x 0) := by simpa only [hxp] using hT
  have hflag : aPoint x ≤ bStar := by simpa only [hax] using hcase
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e88 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
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
.mul 4 2,
.const (2159811/5000000 : ℚ),
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
.const (15562059649518128248733312094092471/5010122273867260946776040999324726025 : ℚ),
.const (290893323061380864622400000000000000/200404890954690437871041639972989041 : ℚ),
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
private noncomputable def ssaQVals : Fin 15 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(2159811/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(15562059649518128248733312094092471/5010122273867260946776040999324726025 : ℚ),(290893323061380864622400000000000000/200404890954690437871041639972989041 : ℚ),(145513/100000 : ℚ),(-113609/200000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
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
private noncomputable def denominator : Int := 1730727688104637613294981503718009619061157786400785871692851182147993600000000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨1658614034433611161456203148038933437932376459834727731116168142944218646190078809866240000000,1676642447851367687879513331726821818465496605575761313202449582705868800000000000000000000000⟩,⟨0,1730727688104637613294981503718009619061157786400785871692851182147993600000000000000000000000⟩,⟨0,1730727688104637613294981503718009619061157786400785871692851182147993600000000000000000000000⟩,⟨0,1730727688104637613294981503718009619061157786400785871692851182147993600000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 3 true
private noncomputable def ibox2 : Fin 4 → FixedTape.I := splitI ibox1 1 865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 1 432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := faceI ibox4 0 true
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox3 1 216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 true
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 2 865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox6 2 865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox8 1 324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 false
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox8 1 324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 true
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox2 1 432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox11 1 649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 false
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox12 2 865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 false
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox13 1 540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 false
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox13 1 540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 true
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox12 2 865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 true
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 1 540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := faceI ibox17 0 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox16 1 540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := faceI ibox19 0 true
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox11 1 649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 true
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox21 2 865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 false
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox22 1 757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 false
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox22 1 757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 true
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox21 2 865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 true
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox25 1 757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 false
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox26 2 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 false
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox26 2 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 true
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox28 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox28 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox25 1 757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 true
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox31 2 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 false
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox31 2 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 true
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox33 1 811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 false
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox33 1 811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 true
private noncomputable def ibox36 : Fin 4 → FixedTape.I := splitI ibox1 1 865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 true
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox36 1 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 false
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox37 1 1081704805065398508309363439823756011913223616500491169808031988842496000000000000000000000000 false
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox38 2 865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 false
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox39 1 973534324558858657478427095841380410721901254850442052827228789958246400000000000000000000000 false
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox39 1 973534324558858657478427095841380410721901254850442052827228789958246400000000000000000000000 true
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox41 1 1027619564812128582893895267832568211317562435675466611317630389400371200000000000000000000000 false
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox41 1 1027619564812128582893895267832568211317562435675466611317630389400371200000000000000000000000 true
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox38 2 865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 true
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox44 1 973534324558858657478427095841380410721901254850442052827228789958246400000000000000000000000 false
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox45 2 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 false
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox45 2 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 true
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox47 1 919449084305588732062958923850192610126240074025417494336827190516121600000000000000000000000 false
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox47 1 919449084305588732062958923850192610126240074025417494336827190516121600000000000000000000000 true
private noncomputable def ibox50 : Fin 4 → FixedTape.I := faceI ibox49 0 true
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox44 1 973534324558858657478427095841380410721901254850442052827228789958246400000000000000000000000 true
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox51 2 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 false
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox52 1 1027619564812128582893895267832568211317562435675466611317630389400371200000000000000000000000 false
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox52 1 1027619564812128582893895267832568211317562435675466611317630389400371200000000000000000000000 true
private noncomputable def ibox55 : Fin 4 → FixedTape.I := splitI ibox51 2 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 true
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox55 1 1027619564812128582893895267832568211317562435675466611317630389400371200000000000000000000000 false
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox56 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 false
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox56 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 true
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox55 1 1027619564812128582893895267832568211317562435675466611317630389400371200000000000000000000000 true
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox59 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 false
private noncomputable def ibox61 : Fin 4 → FixedTape.I := splitI ibox59 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 true
private noncomputable def ibox62 : Fin 4 → FixedTape.I := splitI ibox37 1 1081704805065398508309363439823756011913223616500491169808031988842496000000000000000000000000 true
private noncomputable def ibox63 : Fin 4 → FixedTape.I := splitI ibox62 2 865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 false
private noncomputable def ibox64 : Fin 4 → FixedTape.I := splitI ibox63 1 1189875285571938359140299783806131613104545978150540286788835187726745600000000000000000000000 false
private noncomputable def ibox65 : Fin 4 → FixedTape.I := splitI ibox64 1 1135790045318668433724831611814943812508884797325515728298433588284620800000000000000000000000 false
private noncomputable def ibox66 : Fin 4 → FixedTape.I := splitI ibox64 1 1135790045318668433724831611814943812508884797325515728298433588284620800000000000000000000000 true
private noncomputable def ibox67 : Fin 4 → FixedTape.I := splitI ibox63 1 1189875285571938359140299783806131613104545978150540286788835187726745600000000000000000000000 true
private noncomputable def ibox68 : Fin 4 → FixedTape.I := splitI ibox67 1 1243960525825208284555767955797319413700207158975564845279236787168870400000000000000000000000 false
private noncomputable def ibox69 : Fin 4 → FixedTape.I := splitI ibox67 1 1243960525825208284555767955797319413700207158975564845279236787168870400000000000000000000000 true
private noncomputable def ibox70 : Fin 4 → FixedTape.I := splitI ibox62 2 865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 true
private noncomputable def ibox71 : Fin 4 → FixedTape.I := splitI ibox70 1 1189875285571938359140299783806131613104545978150540286788835187726745600000000000000000000000 false
private noncomputable def ibox72 : Fin 4 → FixedTape.I := splitI ibox71 2 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 false
private noncomputable def ibox73 : Fin 4 → FixedTape.I := splitI ibox72 1 1135790045318668433724831611814943812508884797325515728298433588284620800000000000000000000000 false
private noncomputable def ibox74 : Fin 4 → FixedTape.I := splitI ibox72 1 1135790045318668433724831611814943812508884797325515728298433588284620800000000000000000000000 true
private noncomputable def ibox75 : Fin 4 → FixedTape.I := splitI ibox71 2 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 true
private noncomputable def ibox76 : Fin 4 → FixedTape.I := splitI ibox75 1 1135790045318668433724831611814943812508884797325515728298433588284620800000000000000000000000 false
private noncomputable def ibox77 : Fin 4 → FixedTape.I := splitI ibox76 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 false
private noncomputable def ibox78 : Fin 4 → FixedTape.I := splitI ibox76 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 true
private noncomputable def ibox79 : Fin 4 → FixedTape.I := splitI ibox75 1 1135790045318668433724831611814943812508884797325515728298433588284620800000000000000000000000 true
private noncomputable def ibox80 : Fin 4 → FixedTape.I := splitI ibox79 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 false
private noncomputable def ibox81 : Fin 4 → FixedTape.I := splitI ibox79 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 true
private noncomputable def ibox82 : Fin 4 → FixedTape.I := splitI ibox81 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox83 : Fin 4 → FixedTape.I := splitI ibox81 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox84 : Fin 4 → FixedTape.I := splitI ibox70 1 1189875285571938359140299783806131613104545978150540286788835187726745600000000000000000000000 true
private noncomputable def ibox85 : Fin 4 → FixedTape.I := splitI ibox84 2 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 false
private noncomputable def ibox86 : Fin 4 → FixedTape.I := splitI ibox85 1 1243960525825208284555767955797319413700207158975564845279236787168870400000000000000000000000 false
private noncomputable def ibox87 : Fin 4 → FixedTape.I := splitI ibox85 1 1243960525825208284555767955797319413700207158975564845279236787168870400000000000000000000000 true
private noncomputable def ibox88 : Fin 4 → FixedTape.I := splitI ibox84 2 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 true
private noncomputable def ibox89 : Fin 4 → FixedTape.I := splitI ibox88 1 1243960525825208284555767955797319413700207158975564845279236787168870400000000000000000000000 false
private noncomputable def ibox90 : Fin 4 → FixedTape.I := splitI ibox89 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 false
private noncomputable def ibox91 : Fin 4 → FixedTape.I := splitI ibox89 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 true
private noncomputable def ibox92 : Fin 4 → FixedTape.I := splitI ibox91 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox93 : Fin 4 → FixedTape.I := splitI ibox91 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox94 : Fin 4 → FixedTape.I := splitI ibox88 1 1243960525825208284555767955797319413700207158975564845279236787168870400000000000000000000000 true
private noncomputable def ibox95 : Fin 4 → FixedTape.I := splitI ibox94 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 false
private noncomputable def ibox96 : Fin 4 → FixedTape.I := splitI ibox94 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 true
private noncomputable def ibox97 : Fin 4 → FixedTape.I := splitI ibox96 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox98 : Fin 4 → FixedTape.I := splitI ibox96 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox99 : Fin 4 → FixedTape.I := splitI ibox36 1 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 true
private noncomputable def ibox100 : Fin 4 → FixedTape.I := splitI ibox99 1 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 false
private noncomputable def ibox101 : Fin 4 → FixedTape.I := splitI ibox100 2 865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 false
private noncomputable def ibox102 : Fin 4 → FixedTape.I := splitI ibox101 1 1406216246585018060802172471770882815487190701450638520750441585495244800000000000000000000000 false
private noncomputable def ibox103 : Fin 4 → FixedTape.I := splitI ibox102 1 1352131006331748135386704299779695014891529520625613962260039986053120000000000000000000000000 false
private noncomputable def ibox104 : Fin 4 → FixedTape.I := splitI ibox102 1 1352131006331748135386704299779695014891529520625613962260039986053120000000000000000000000000 true
private noncomputable def ibox105 : Fin 4 → FixedTape.I := splitI ibox101 1 1406216246585018060802172471770882815487190701450638520750441585495244800000000000000000000000 true
private noncomputable def ibox106 : Fin 4 → FixedTape.I := splitI ibox105 1 1460301486838287986217640643762070616082851882275663079240843184937369600000000000000000000000 false
private noncomputable def ibox107 : Fin 4 → FixedTape.I := splitI ibox105 1 1460301486838287986217640643762070616082851882275663079240843184937369600000000000000000000000 true
private noncomputable def ibox108 : Fin 4 → FixedTape.I := splitI ibox107 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox109 : Fin 4 → FixedTape.I := splitI ibox107 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox110 : Fin 4 → FixedTape.I := splitI ibox100 2 865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 true
private noncomputable def ibox111 : Fin 4 → FixedTape.I := splitI ibox110 1 1406216246585018060802172471770882815487190701450638520750441585495244800000000000000000000000 false
private noncomputable def ibox112 : Fin 4 → FixedTape.I := splitI ibox111 2 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 false
private noncomputable def ibox113 : Fin 4 → FixedTape.I := splitI ibox112 1 1352131006331748135386704299779695014891529520625613962260039986053120000000000000000000000000 false
private noncomputable def ibox114 : Fin 4 → FixedTape.I := splitI ibox112 1 1352131006331748135386704299779695014891529520625613962260039986053120000000000000000000000000 true
private noncomputable def ibox115 : Fin 4 → FixedTape.I := splitI ibox111 2 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 true
private noncomputable def ibox116 : Fin 4 → FixedTape.I := splitI ibox115 1 1352131006331748135386704299779695014891529520625613962260039986053120000000000000000000000000 false
private noncomputable def ibox117 : Fin 4 → FixedTape.I := splitI ibox116 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 false
private noncomputable def ibox118 : Fin 4 → FixedTape.I := splitI ibox116 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 true
private noncomputable def ibox119 : Fin 4 → FixedTape.I := splitI ibox118 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox120 : Fin 4 → FixedTape.I := splitI ibox118 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox121 : Fin 4 → FixedTape.I := splitI ibox115 1 1352131006331748135386704299779695014891529520625613962260039986053120000000000000000000000000 true
private noncomputable def ibox122 : Fin 4 → FixedTape.I := splitI ibox121 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 false
private noncomputable def ibox123 : Fin 4 → FixedTape.I := splitI ibox121 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 true
private noncomputable def ibox124 : Fin 4 → FixedTape.I := splitI ibox123 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox125 : Fin 4 → FixedTape.I := splitI ibox123 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox126 : Fin 4 → FixedTape.I := splitI ibox110 1 1406216246585018060802172471770882815487190701450638520750441585495244800000000000000000000000 true
private noncomputable def ibox127 : Fin 4 → FixedTape.I := splitI ibox126 2 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 false
private noncomputable def ibox128 : Fin 4 → FixedTape.I := splitI ibox127 1 1460301486838287986217640643762070616082851882275663079240843184937369600000000000000000000000 false
private noncomputable def ibox129 : Fin 4 → FixedTape.I := splitI ibox127 1 1460301486838287986217640643762070616082851882275663079240843184937369600000000000000000000000 true
private noncomputable def ibox130 : Fin 4 → FixedTape.I := splitI ibox129 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox131 : Fin 4 → FixedTape.I := splitI ibox129 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox132 : Fin 4 → FixedTape.I := splitI ibox126 2 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 true
private noncomputable def ibox133 : Fin 4 → FixedTape.I := splitI ibox132 1 1460301486838287986217640643762070616082851882275663079240843184937369600000000000000000000000 false
private noncomputable def ibox134 : Fin 4 → FixedTape.I := splitI ibox133 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 false
private noncomputable def ibox135 : Fin 4 → FixedTape.I := splitI ibox134 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox136 : Fin 4 → FixedTape.I := splitI ibox134 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox137 : Fin 4 → FixedTape.I := splitI ibox133 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 true
private noncomputable def ibox138 : Fin 4 → FixedTape.I := splitI ibox137 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox139 : Fin 4 → FixedTape.I := splitI ibox137 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox140 : Fin 4 → FixedTape.I := splitI ibox132 1 1460301486838287986217640643762070616082851882275663079240843184937369600000000000000000000000 true
private noncomputable def ibox141 : Fin 4 → FixedTape.I := splitI ibox140 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 false
private noncomputable def ibox142 : Fin 4 → FixedTape.I := splitI ibox141 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox143 : Fin 4 → FixedTape.I := splitI ibox141 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox144 : Fin 4 → FixedTape.I := splitI ibox140 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 true
private noncomputable def ibox145 : Fin 4 → FixedTape.I := splitI ibox144 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox146 : Fin 4 → FixedTape.I := splitI ibox144 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox147 : Fin 4 → FixedTape.I := splitI ibox99 1 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 true
private noncomputable def ibox148 : Fin 4 → FixedTape.I := splitI ibox147 2 865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 false
private noncomputable def ibox149 : Fin 4 → FixedTape.I := splitI ibox148 1 1622557207598097762464045159735634017869835424750736754712047983263744000000000000000000000000 false
private noncomputable def ibox150 : Fin 4 → FixedTape.I := splitI ibox149 1 1568471967344827837048576987744446217274174243925712196221646383821619200000000000000000000000 false
private noncomputable def ibox151 : Fin 4 → FixedTape.I := splitI ibox150 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox152 : Fin 4 → FixedTape.I := splitI ibox150 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox153 : Fin 4 → FixedTape.I := splitI ibox149 1 1568471967344827837048576987744446217274174243925712196221646383821619200000000000000000000000 true
private noncomputable def ibox154 : Fin 4 → FixedTape.I := splitI ibox153 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox155 : Fin 4 → FixedTape.I := splitI ibox153 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox156 : Fin 4 → FixedTape.I := splitI ibox148 1 1622557207598097762464045159735634017869835424750736754712047983263744000000000000000000000000 true
private noncomputable def ibox157 : Fin 4 → FixedTape.I := splitI ibox156 1 1676642447851367687879513331726821818465496605575761313202449582705868800000000000000000000000 false
private noncomputable def ibox158 : Fin 4 → FixedTape.I := splitI ibox157 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox159 : Fin 4 → FixedTape.I := splitI ibox157 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox160 : Fin 4 → FixedTape.I := splitI ibox156 1 1676642447851367687879513331726821818465496605575761313202449582705868800000000000000000000000 true
private noncomputable def ibox161 : Fin 4 → FixedTape.I := splitI ibox160 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox162 : Fin 4 → FixedTape.I := splitI ibox160 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox163 : Fin 4 → FixedTape.I := splitI ibox147 2 865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 true
private noncomputable def ibox164 : Fin 4 → FixedTape.I := splitI ibox163 1 1622557207598097762464045159735634017869835424750736754712047983263744000000000000000000000000 false
private noncomputable def ibox165 : Fin 4 → FixedTape.I := splitI ibox164 2 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 false
private noncomputable def ibox166 : Fin 4 → FixedTape.I := splitI ibox165 1 1568471967344827837048576987744446217274174243925712196221646383821619200000000000000000000000 false
private noncomputable def ibox167 : Fin 4 → FixedTape.I := splitI ibox166 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox168 : Fin 4 → FixedTape.I := splitI ibox166 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox169 : Fin 4 → FixedTape.I := splitI ibox165 1 1568471967344827837048576987744446217274174243925712196221646383821619200000000000000000000000 true
private noncomputable def ibox170 : Fin 4 → FixedTape.I := splitI ibox169 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox171 : Fin 4 → FixedTape.I := splitI ibox169 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox172 : Fin 4 → FixedTape.I := splitI ibox164 2 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 true
private noncomputable def ibox173 : Fin 4 → FixedTape.I := splitI ibox172 1 1568471967344827837048576987744446217274174243925712196221646383821619200000000000000000000000 false
private noncomputable def ibox174 : Fin 4 → FixedTape.I := splitI ibox173 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 false
private noncomputable def ibox175 : Fin 4 → FixedTape.I := splitI ibox174 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox176 : Fin 4 → FixedTape.I := splitI ibox174 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox177 : Fin 4 → FixedTape.I := splitI ibox173 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 true
private noncomputable def ibox178 : Fin 4 → FixedTape.I := splitI ibox177 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox179 : Fin 4 → FixedTape.I := splitI ibox177 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox180 : Fin 4 → FixedTape.I := splitI ibox172 1 1568471967344827837048576987744446217274174243925712196221646383821619200000000000000000000000 true
private noncomputable def ibox181 : Fin 4 → FixedTape.I := splitI ibox180 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 false
private noncomputable def ibox182 : Fin 4 → FixedTape.I := splitI ibox181 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox183 : Fin 4 → FixedTape.I := splitI ibox181 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox184 : Fin 4 → FixedTape.I := splitI ibox180 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 true
private noncomputable def ibox185 : Fin 4 → FixedTape.I := splitI ibox184 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox186 : Fin 4 → FixedTape.I := splitI ibox184 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox187 : Fin 4 → FixedTape.I := splitI ibox163 1 1622557207598097762464045159735634017869835424750736754712047983263744000000000000000000000000 true
private noncomputable def ibox188 : Fin 4 → FixedTape.I := splitI ibox187 2 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 false
private noncomputable def ibox189 : Fin 4 → FixedTape.I := splitI ibox188 1 1676642447851367687879513331726821818465496605575761313202449582705868800000000000000000000000 false
private noncomputable def ibox190 : Fin 4 → FixedTape.I := splitI ibox189 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox191 : Fin 4 → FixedTape.I := splitI ibox189 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox192 : Fin 4 → FixedTape.I := splitI ibox188 1 1676642447851367687879513331726821818465496605575761313202449582705868800000000000000000000000 true
private noncomputable def ibox193 : Fin 4 → FixedTape.I := splitI ibox192 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox194 : Fin 4 → FixedTape.I := splitI ibox192 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox195 : Fin 4 → FixedTape.I := splitI ibox187 2 1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 true
private noncomputable def ibox196 : Fin 4 → FixedTape.I := splitI ibox195 1 1676642447851367687879513331726821818465496605575761313202449582705868800000000000000000000000 false
private noncomputable def ibox197 : Fin 4 → FixedTape.I := splitI ibox196 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 false
private noncomputable def ibox198 : Fin 4 → FixedTape.I := splitI ibox197 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox199 : Fin 4 → FixedTape.I := splitI ibox197 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox200 : Fin 4 → FixedTape.I := splitI ibox196 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 true
private noncomputable def ibox201 : Fin 4 → FixedTape.I := splitI ibox200 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox202 : Fin 4 → FixedTape.I := splitI ibox200 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox203 : Fin 4 → FixedTape.I := splitI ibox202 0 1672135344496928556273685785804849723332216569140502917680879222765456261547519702466560000000 false
private noncomputable def ibox204 : Fin 4 → FixedTape.I := splitI ibox202 0 1672135344496928556273685785804849723332216569140502917680879222765456261547519702466560000000 true
private noncomputable def ibox205 : Fin 4 → FixedTape.I := splitI ibox195 1 1676642447851367687879513331726821818465496605575761313202449582705868800000000000000000000000 true
private noncomputable def ibox206 : Fin 4 → FixedTape.I := splitI ibox205 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 false
private noncomputable def ibox207 : Fin 4 → FixedTape.I := splitI ibox206 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox208 : Fin 4 → FixedTape.I := splitI ibox206 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox209 : Fin 4 → FixedTape.I := splitI ibox205 2 1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 true
private noncomputable def ibox210 : Fin 4 → FixedTape.I := splitI ibox209 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 false
private noncomputable def ibox211 : Fin 4 → FixedTape.I := splitI ibox209 0 1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 true
private noncomputable def ibox212 : Fin 4 → FixedTape.I := splitI ibox211 1 1703685067978002650587247417722415718763327195988273592447650382426931200000000000000000000000 false
private noncomputable def ibox213 : Fin 4 → FixedTape.I := splitI ibox211 1 1703685067978002650587247417722415718763327195988273592447650382426931200000000000000000000000 true
private noncomputable def tree213 : TapeTree := .centered (candidateRows ibox213) (candidateRows (FixedTape.midBox ibox213))
attribute [irreducible] tree213
private theorem sign_213 : 2*denominator*(computed denominator (FixedTape.midBox ibox213)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox213).gradient k).lo.natAbs ((computed denominator ibox213).gradient k).hi.natAbs : Int)*((ibox213 k).hi-(ibox213 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox213
    (computed denominator ibox213) (computed denominator (FixedTape.midBox ibox213))
    (by decide +kernel)
private theorem midpoint_even_213 : ∀ k, 2 ∣ (ibox213 k).lo+(ibox213 k).hi := by decide +kernel
private theorem accepted_213 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox213) tree213 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox213 midpoint_even_213
  simp only [tree213,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox213,candidate_valid h (FixedTape.midBox ibox213),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox213 83 (FixedTape.rowsAux denominator ibox213 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox213) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_213
private noncomputable def tree212 : TapeTree := .centered (candidateRows ibox212) (candidateRows (FixedTape.midBox ibox212))
attribute [irreducible] tree212
private theorem sign_212 : 2*denominator*(computed denominator (FixedTape.midBox ibox212)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox212).gradient k).lo.natAbs ((computed denominator ibox212).gradient k).hi.natAbs : Int)*((ibox212 k).hi-(ibox212 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox212
    (computed denominator ibox212) (computed denominator (FixedTape.midBox ibox212))
    (by decide +kernel)
private theorem midpoint_even_212 : ∀ k, 2 ∣ (ibox212 k).lo+(ibox212 k).hi := by decide +kernel
private theorem accepted_212 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox212) tree212 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox212 midpoint_even_212
  simp only [tree212,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox212,candidate_valid h (FixedTape.midBox ibox212),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox212 83 (FixedTape.rowsAux denominator ibox212 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox212) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_212
private noncomputable def tree211 : TapeTree := .split 1 (((1703685067978002650587247417722415718763327195988273592447650382426931200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree212 tree213
attribute [irreducible] tree211
private theorem accepted_211 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox211) tree211 = true := by
  simp only [tree211,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox211 1 (1703685067978002650587247417722415718763327195988273592447650382426931200000000000000000000000 : Int) false,decode_split denominator ibox211 1 (1703685067978002650587247417722415718763327195988273592447650382426931200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_212 h,accepted_213 h⟩
private noncomputable def tree210 : TapeTree := .centered (candidateRows ibox210) (candidateRows (FixedTape.midBox ibox210))
attribute [irreducible] tree210
private theorem sign_210 : 2*denominator*(computed denominator (FixedTape.midBox ibox210)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox210).gradient k).lo.natAbs ((computed denominator ibox210).gradient k).hi.natAbs : Int)*((ibox210 k).hi-(ibox210 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox210
    (computed denominator ibox210) (computed denominator (FixedTape.midBox ibox210))
    (by decide +kernel)
private theorem midpoint_even_210 : ∀ k, 2 ∣ (ibox210 k).lo+(ibox210 k).hi := by decide +kernel
private theorem accepted_210 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox210) tree210 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox210 midpoint_even_210
  simp only [tree210,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox210,candidate_valid h (FixedTape.midBox ibox210),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox210 83 (FixedTape.rowsAux denominator ibox210 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox210) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_210
private noncomputable def tree209 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree210 tree211
attribute [irreducible] tree209
private theorem accepted_209 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox209) tree209 = true := by
  simp only [tree209,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox209 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox209 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_210 h,accepted_211 h⟩
private noncomputable def tree208 : TapeTree := .centered (candidateRows ibox208) (candidateRows (FixedTape.midBox ibox208))
attribute [irreducible] tree208
private theorem sign_208 : 2*denominator*(computed denominator (FixedTape.midBox ibox208)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox208).gradient k).lo.natAbs ((computed denominator ibox208).gradient k).hi.natAbs : Int)*((ibox208 k).hi-(ibox208 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox208
    (computed denominator ibox208) (computed denominator (FixedTape.midBox ibox208))
    (by decide +kernel)
private theorem midpoint_even_208 : ∀ k, 2 ∣ (ibox208 k).lo+(ibox208 k).hi := by decide +kernel
private theorem accepted_208 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox208) tree208 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox208 midpoint_even_208
  simp only [tree208,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox208,candidate_valid h (FixedTape.midBox ibox208),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox208 83 (FixedTape.rowsAux denominator ibox208 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox208) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_208
private noncomputable def tree207 : TapeTree := .centered (candidateRows ibox207) (candidateRows (FixedTape.midBox ibox207))
attribute [irreducible] tree207
private theorem sign_207 : 2*denominator*(computed denominator (FixedTape.midBox ibox207)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox207).gradient k).lo.natAbs ((computed denominator ibox207).gradient k).hi.natAbs : Int)*((ibox207 k).hi-(ibox207 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox207
    (computed denominator ibox207) (computed denominator (FixedTape.midBox ibox207))
    (by decide +kernel)
private theorem midpoint_even_207 : ∀ k, 2 ∣ (ibox207 k).lo+(ibox207 k).hi := by decide +kernel
private theorem accepted_207 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox207) tree207 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox207 midpoint_even_207
  simp only [tree207,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox207,candidate_valid h (FixedTape.midBox ibox207),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox207 83 (FixedTape.rowsAux denominator ibox207 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox207) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_207
private noncomputable def tree206 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree207 tree208
attribute [irreducible] tree206
private theorem accepted_206 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox206) tree206 = true := by
  simp only [tree206,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox206 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox206 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_207 h,accepted_208 h⟩
private noncomputable def tree205 : TapeTree := .split 2 (((1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree206 tree209
attribute [irreducible] tree205
private theorem accepted_205 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox205) tree205 = true := by
  simp only [tree205,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox205 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) false,decode_split denominator ibox205 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_206 h,accepted_209 h⟩
private noncomputable def tree204 : TapeTree := .centered (candidateRows ibox204) (candidateRows (FixedTape.midBox ibox204))
attribute [irreducible] tree204
private theorem sign_204 : 2*denominator*(computed denominator (FixedTape.midBox ibox204)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox204).gradient k).lo.natAbs ((computed denominator ibox204).gradient k).hi.natAbs : Int)*((ibox204 k).hi-(ibox204 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox204
    (computed denominator ibox204) (computed denominator (FixedTape.midBox ibox204))
    (by decide +kernel)
private theorem midpoint_even_204 : ∀ k, 2 ∣ (ibox204 k).lo+(ibox204 k).hi := by decide +kernel
private theorem accepted_204 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox204) tree204 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox204 midpoint_even_204
  simp only [tree204,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox204,candidate_valid h (FixedTape.midBox ibox204),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox204 83 (FixedTape.rowsAux denominator ibox204 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox204) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_204
private noncomputable def tree203 : TapeTree := .centered (candidateRows ibox203) (candidateRows (FixedTape.midBox ibox203))
attribute [irreducible] tree203
private theorem sign_203 : 2*denominator*(computed denominator (FixedTape.midBox ibox203)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox203).gradient k).lo.natAbs ((computed denominator ibox203).gradient k).hi.natAbs : Int)*((ibox203 k).hi-(ibox203 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox203
    (computed denominator ibox203) (computed denominator (FixedTape.midBox ibox203))
    (by decide +kernel)
private theorem midpoint_even_203 : ∀ k, 2 ∣ (ibox203 k).lo+(ibox203 k).hi := by decide +kernel
private theorem accepted_203 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox203) tree203 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox203 midpoint_even_203
  simp only [tree203,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox203,candidate_valid h (FixedTape.midBox ibox203),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox203 83 (FixedTape.rowsAux denominator ibox203 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox203) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_203
private noncomputable def tree202 : TapeTree := .split 0 (((1672135344496928556273685785804849723332216569140502917680879222765456261547519702466560000000 : Int) : ℚ)/(denominator : ℚ)) tree203 tree204
attribute [irreducible] tree202
private theorem accepted_202 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox202) tree202 = true := by
  simp only [tree202,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox202 0 (1672135344496928556273685785804849723332216569140502917680879222765456261547519702466560000000 : Int) false,decode_split denominator ibox202 0 (1672135344496928556273685785804849723332216569140502917680879222765456261547519702466560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_203 h,accepted_204 h⟩
private noncomputable def tree201 : TapeTree := .centered (candidateRows ibox201) (candidateRows (FixedTape.midBox ibox201))
attribute [irreducible] tree201
private theorem sign_201 : 2*denominator*(computed denominator (FixedTape.midBox ibox201)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox201).gradient k).lo.natAbs ((computed denominator ibox201).gradient k).hi.natAbs : Int)*((ibox201 k).hi-(ibox201 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox201
    (computed denominator ibox201) (computed denominator (FixedTape.midBox ibox201))
    (by decide +kernel)
private theorem midpoint_even_201 : ∀ k, 2 ∣ (ibox201 k).lo+(ibox201 k).hi := by decide +kernel
private theorem accepted_201 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox201) tree201 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox201 midpoint_even_201
  simp only [tree201,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox201,candidate_valid h (FixedTape.midBox ibox201),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox201 83 (FixedTape.rowsAux denominator ibox201 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox201) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_201
private noncomputable def tree200 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree201 tree202
attribute [irreducible] tree200
private theorem accepted_200 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox200) tree200 = true := by
  simp only [tree200,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox200 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox200 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_201 h,accepted_202 h⟩
private noncomputable def tree199 : TapeTree := .centered (candidateRows ibox199) (candidateRows (FixedTape.midBox ibox199))
attribute [irreducible] tree199
private theorem sign_199 : 2*denominator*(computed denominator (FixedTape.midBox ibox199)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox199).gradient k).lo.natAbs ((computed denominator ibox199).gradient k).hi.natAbs : Int)*((ibox199 k).hi-(ibox199 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox199
    (computed denominator ibox199) (computed denominator (FixedTape.midBox ibox199))
    (by decide +kernel)
private theorem midpoint_even_199 : ∀ k, 2 ∣ (ibox199 k).lo+(ibox199 k).hi := by decide +kernel
private theorem accepted_199 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox199) tree199 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox199 midpoint_even_199
  simp only [tree199,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox199,candidate_valid h (FixedTape.midBox ibox199),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox199 83 (FixedTape.rowsAux denominator ibox199 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox199) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_199
private noncomputable def tree198 : TapeTree := .centered (candidateRows ibox198) (candidateRows (FixedTape.midBox ibox198))
attribute [irreducible] tree198
private theorem sign_198 : 2*denominator*(computed denominator (FixedTape.midBox ibox198)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox198).gradient k).lo.natAbs ((computed denominator ibox198).gradient k).hi.natAbs : Int)*((ibox198 k).hi-(ibox198 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox198
    (computed denominator ibox198) (computed denominator (FixedTape.midBox ibox198))
    (by decide +kernel)
private theorem midpoint_even_198 : ∀ k, 2 ∣ (ibox198 k).lo+(ibox198 k).hi := by decide +kernel
private theorem accepted_198 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox198) tree198 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox198 midpoint_even_198
  simp only [tree198,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox198,candidate_valid h (FixedTape.midBox ibox198),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox198 83 (FixedTape.rowsAux denominator ibox198 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox198) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_198
private noncomputable def tree197 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree198 tree199
attribute [irreducible] tree197
private theorem accepted_197 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox197) tree197 = true := by
  simp only [tree197,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox197 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox197 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_198 h,accepted_199 h⟩
private noncomputable def tree196 : TapeTree := .split 2 (((1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree197 tree200
attribute [irreducible] tree196
private theorem accepted_196 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox196) tree196 = true := by
  simp only [tree196,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox196 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) false,decode_split denominator ibox196 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_197 h,accepted_200 h⟩
private noncomputable def tree195 : TapeTree := .split 1 (((1676642447851367687879513331726821818465496605575761313202449582705868800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree196 tree205
attribute [irreducible] tree195
private theorem accepted_195 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox195) tree195 = true := by
  simp only [tree195,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox195 1 (1676642447851367687879513331726821818465496605575761313202449582705868800000000000000000000000 : Int) false,decode_split denominator ibox195 1 (1676642447851367687879513331726821818465496605575761313202449582705868800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_196 h,accepted_205 h⟩
private noncomputable def tree194 : TapeTree := .centered (candidateRows ibox194) (candidateRows (FixedTape.midBox ibox194))
attribute [irreducible] tree194
private theorem sign_194 : 2*denominator*(computed denominator (FixedTape.midBox ibox194)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox194).gradient k).lo.natAbs ((computed denominator ibox194).gradient k).hi.natAbs : Int)*((ibox194 k).hi-(ibox194 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox194
    (computed denominator ibox194) (computed denominator (FixedTape.midBox ibox194))
    (by decide +kernel)
private theorem midpoint_even_194 : ∀ k, 2 ∣ (ibox194 k).lo+(ibox194 k).hi := by decide +kernel
private theorem accepted_194 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox194) tree194 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox194 midpoint_even_194
  simp only [tree194,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox194,candidate_valid h (FixedTape.midBox ibox194),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox194 83 (FixedTape.rowsAux denominator ibox194 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox194) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_194
private noncomputable def tree193 : TapeTree := .centered (candidateRows ibox193) (candidateRows (FixedTape.midBox ibox193))
attribute [irreducible] tree193
private theorem sign_193 : 2*denominator*(computed denominator (FixedTape.midBox ibox193)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox193).gradient k).lo.natAbs ((computed denominator ibox193).gradient k).hi.natAbs : Int)*((ibox193 k).hi-(ibox193 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox193
    (computed denominator ibox193) (computed denominator (FixedTape.midBox ibox193))
    (by decide +kernel)
private theorem midpoint_even_193 : ∀ k, 2 ∣ (ibox193 k).lo+(ibox193 k).hi := by decide +kernel
private theorem accepted_193 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox193) tree193 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox193 midpoint_even_193
  simp only [tree193,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox193,candidate_valid h (FixedTape.midBox ibox193),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox193 83 (FixedTape.rowsAux denominator ibox193 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox193) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_193
private noncomputable def tree192 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree193 tree194
attribute [irreducible] tree192
private theorem accepted_192 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox192) tree192 = true := by
  simp only [tree192,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox192 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox192 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_193 h,accepted_194 h⟩
private noncomputable def tree191 : TapeTree := .centered (candidateRows ibox191) (candidateRows (FixedTape.midBox ibox191))
attribute [irreducible] tree191
private theorem sign_191 : 2*denominator*(computed denominator (FixedTape.midBox ibox191)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox191).gradient k).lo.natAbs ((computed denominator ibox191).gradient k).hi.natAbs : Int)*((ibox191 k).hi-(ibox191 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox191
    (computed denominator ibox191) (computed denominator (FixedTape.midBox ibox191))
    (by decide +kernel)
private theorem midpoint_even_191 : ∀ k, 2 ∣ (ibox191 k).lo+(ibox191 k).hi := by decide +kernel
private theorem accepted_191 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox191) tree191 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox191 midpoint_even_191
  simp only [tree191,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox191,candidate_valid h (FixedTape.midBox ibox191),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox191 83 (FixedTape.rowsAux denominator ibox191 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox191) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_191
private noncomputable def tree190 : TapeTree := .centered (candidateRows ibox190) (candidateRows (FixedTape.midBox ibox190))
attribute [irreducible] tree190
private theorem sign_190 : 2*denominator*(computed denominator (FixedTape.midBox ibox190)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox190).gradient k).lo.natAbs ((computed denominator ibox190).gradient k).hi.natAbs : Int)*((ibox190 k).hi-(ibox190 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox190
    (computed denominator ibox190) (computed denominator (FixedTape.midBox ibox190))
    (by decide +kernel)
private theorem midpoint_even_190 : ∀ k, 2 ∣ (ibox190 k).lo+(ibox190 k).hi := by decide +kernel
private theorem accepted_190 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox190) tree190 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox190 midpoint_even_190
  simp only [tree190,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox190,candidate_valid h (FixedTape.midBox ibox190),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox190 83 (FixedTape.rowsAux denominator ibox190 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox190) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_190
private noncomputable def tree189 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree190 tree191
attribute [irreducible] tree189
private theorem accepted_189 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox189) tree189 = true := by
  simp only [tree189,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox189 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox189 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_190 h,accepted_191 h⟩
private noncomputable def tree188 : TapeTree := .split 1 (((1676642447851367687879513331726821818465496605575761313202449582705868800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree189 tree192
attribute [irreducible] tree188
private theorem accepted_188 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox188) tree188 = true := by
  simp only [tree188,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox188 1 (1676642447851367687879513331726821818465496605575761313202449582705868800000000000000000000000 : Int) false,decode_split denominator ibox188 1 (1676642447851367687879513331726821818465496605575761313202449582705868800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_189 h,accepted_192 h⟩
private noncomputable def tree187 : TapeTree := .split 2 (((1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree188 tree195
attribute [irreducible] tree187
private theorem accepted_187 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox187) tree187 = true := by
  simp only [tree187,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox187 2 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) false,decode_split denominator ibox187 2 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_188 h,accepted_195 h⟩
private noncomputable def tree186 : TapeTree := .centered (candidateRows ibox186) (candidateRows (FixedTape.midBox ibox186))
attribute [irreducible] tree186
private theorem sign_186 : 2*denominator*(computed denominator (FixedTape.midBox ibox186)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox186).gradient k).lo.natAbs ((computed denominator ibox186).gradient k).hi.natAbs : Int)*((ibox186 k).hi-(ibox186 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox186
    (computed denominator ibox186) (computed denominator (FixedTape.midBox ibox186))
    (by decide +kernel)
private theorem midpoint_even_186 : ∀ k, 2 ∣ (ibox186 k).lo+(ibox186 k).hi := by decide +kernel
private theorem accepted_186 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox186) tree186 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox186 midpoint_even_186
  simp only [tree186,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox186,candidate_valid h (FixedTape.midBox ibox186),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox186 83 (FixedTape.rowsAux denominator ibox186 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox186) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_186
private noncomputable def tree185 : TapeTree := .centered (candidateRows ibox185) (candidateRows (FixedTape.midBox ibox185))
attribute [irreducible] tree185
private theorem sign_185 : 2*denominator*(computed denominator (FixedTape.midBox ibox185)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox185).gradient k).lo.natAbs ((computed denominator ibox185).gradient k).hi.natAbs : Int)*((ibox185 k).hi-(ibox185 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox185
    (computed denominator ibox185) (computed denominator (FixedTape.midBox ibox185))
    (by decide +kernel)
private theorem midpoint_even_185 : ∀ k, 2 ∣ (ibox185 k).lo+(ibox185 k).hi := by decide +kernel
private theorem accepted_185 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox185) tree185 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox185 midpoint_even_185
  simp only [tree185,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox185,candidate_valid h (FixedTape.midBox ibox185),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox185 83 (FixedTape.rowsAux denominator ibox185 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox185) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_185
private noncomputable def tree184 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree185 tree186
attribute [irreducible] tree184
private theorem accepted_184 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox184) tree184 = true := by
  simp only [tree184,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox184 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox184 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_185 h,accepted_186 h⟩
private noncomputable def tree183 : TapeTree := .centered (candidateRows ibox183) (candidateRows (FixedTape.midBox ibox183))
attribute [irreducible] tree183
private theorem sign_183 : 2*denominator*(computed denominator (FixedTape.midBox ibox183)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox183).gradient k).lo.natAbs ((computed denominator ibox183).gradient k).hi.natAbs : Int)*((ibox183 k).hi-(ibox183 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox183
    (computed denominator ibox183) (computed denominator (FixedTape.midBox ibox183))
    (by decide +kernel)
private theorem midpoint_even_183 : ∀ k, 2 ∣ (ibox183 k).lo+(ibox183 k).hi := by decide +kernel
private theorem accepted_183 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox183) tree183 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox183 midpoint_even_183
  simp only [tree183,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox183,candidate_valid h (FixedTape.midBox ibox183),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox183 83 (FixedTape.rowsAux denominator ibox183 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox183) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_183
private noncomputable def tree182 : TapeTree := .centered (candidateRows ibox182) (candidateRows (FixedTape.midBox ibox182))
attribute [irreducible] tree182
private theorem sign_182 : 2*denominator*(computed denominator (FixedTape.midBox ibox182)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox182).gradient k).lo.natAbs ((computed denominator ibox182).gradient k).hi.natAbs : Int)*((ibox182 k).hi-(ibox182 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox182
    (computed denominator ibox182) (computed denominator (FixedTape.midBox ibox182))
    (by decide +kernel)
private theorem midpoint_even_182 : ∀ k, 2 ∣ (ibox182 k).lo+(ibox182 k).hi := by decide +kernel
private theorem accepted_182 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox182) tree182 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox182 midpoint_even_182
  simp only [tree182,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox182,candidate_valid h (FixedTape.midBox ibox182),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox182 83 (FixedTape.rowsAux denominator ibox182 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox182) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_182
private noncomputable def tree181 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree182 tree183
attribute [irreducible] tree181
private theorem accepted_181 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox181) tree181 = true := by
  simp only [tree181,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox181 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox181 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_182 h,accepted_183 h⟩
private noncomputable def tree180 : TapeTree := .split 2 (((1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree181 tree184
attribute [irreducible] tree180
private theorem accepted_180 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox180) tree180 = true := by
  simp only [tree180,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox180 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) false,decode_split denominator ibox180 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_181 h,accepted_184 h⟩
private noncomputable def tree179 : TapeTree := .centered (candidateRows ibox179) (candidateRows (FixedTape.midBox ibox179))
attribute [irreducible] tree179
private theorem sign_179 : 2*denominator*(computed denominator (FixedTape.midBox ibox179)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox179).gradient k).lo.natAbs ((computed denominator ibox179).gradient k).hi.natAbs : Int)*((ibox179 k).hi-(ibox179 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox179
    (computed denominator ibox179) (computed denominator (FixedTape.midBox ibox179))
    (by decide +kernel)
private theorem midpoint_even_179 : ∀ k, 2 ∣ (ibox179 k).lo+(ibox179 k).hi := by decide +kernel
private theorem accepted_179 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox179) tree179 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox179 midpoint_even_179
  simp only [tree179,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox179,candidate_valid h (FixedTape.midBox ibox179),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox179 83 (FixedTape.rowsAux denominator ibox179 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox179) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_179
private noncomputable def tree178 : TapeTree := .centered (candidateRows ibox178) (candidateRows (FixedTape.midBox ibox178))
attribute [irreducible] tree178
private theorem sign_178 : 2*denominator*(computed denominator (FixedTape.midBox ibox178)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox178).gradient k).lo.natAbs ((computed denominator ibox178).gradient k).hi.natAbs : Int)*((ibox178 k).hi-(ibox178 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox178
    (computed denominator ibox178) (computed denominator (FixedTape.midBox ibox178))
    (by decide +kernel)
private theorem midpoint_even_178 : ∀ k, 2 ∣ (ibox178 k).lo+(ibox178 k).hi := by decide +kernel
private theorem accepted_178 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox178) tree178 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox178 midpoint_even_178
  simp only [tree178,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox178,candidate_valid h (FixedTape.midBox ibox178),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox178 83 (FixedTape.rowsAux denominator ibox178 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox178) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_178
private noncomputable def tree177 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree178 tree179
attribute [irreducible] tree177
private theorem accepted_177 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox177) tree177 = true := by
  simp only [tree177,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox177 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox177 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_178 h,accepted_179 h⟩
private noncomputable def tree176 : TapeTree := .centered (candidateRows ibox176) (candidateRows (FixedTape.midBox ibox176))
attribute [irreducible] tree176
private theorem sign_176 : 2*denominator*(computed denominator (FixedTape.midBox ibox176)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox176).gradient k).lo.natAbs ((computed denominator ibox176).gradient k).hi.natAbs : Int)*((ibox176 k).hi-(ibox176 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox176
    (computed denominator ibox176) (computed denominator (FixedTape.midBox ibox176))
    (by decide +kernel)
private theorem midpoint_even_176 : ∀ k, 2 ∣ (ibox176 k).lo+(ibox176 k).hi := by decide +kernel
private theorem accepted_176 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox176) tree176 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox176 midpoint_even_176
  simp only [tree176,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox176,candidate_valid h (FixedTape.midBox ibox176),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox176 83 (FixedTape.rowsAux denominator ibox176 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox176) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_176
private noncomputable def tree175 : TapeTree := .centered (candidateRows ibox175) (candidateRows (FixedTape.midBox ibox175))
attribute [irreducible] tree175
private theorem sign_175 : 2*denominator*(computed denominator (FixedTape.midBox ibox175)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox175).gradient k).lo.natAbs ((computed denominator ibox175).gradient k).hi.natAbs : Int)*((ibox175 k).hi-(ibox175 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox175
    (computed denominator ibox175) (computed denominator (FixedTape.midBox ibox175))
    (by decide +kernel)
private theorem midpoint_even_175 : ∀ k, 2 ∣ (ibox175 k).lo+(ibox175 k).hi := by decide +kernel
private theorem accepted_175 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox175) tree175 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox175 midpoint_even_175
  simp only [tree175,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox175,candidate_valid h (FixedTape.midBox ibox175),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox175 83 (FixedTape.rowsAux denominator ibox175 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox175) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_175
private noncomputable def tree174 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree175 tree176
attribute [irreducible] tree174
private theorem accepted_174 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox174) tree174 = true := by
  simp only [tree174,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox174 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox174 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_175 h,accepted_176 h⟩
private noncomputable def tree173 : TapeTree := .split 2 (((1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree174 tree177
attribute [irreducible] tree173
private theorem accepted_173 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox173) tree173 = true := by
  simp only [tree173,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox173 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) false,decode_split denominator ibox173 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_174 h,accepted_177 h⟩
private noncomputable def tree172 : TapeTree := .split 1 (((1568471967344827837048576987744446217274174243925712196221646383821619200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree173 tree180
attribute [irreducible] tree172
private theorem accepted_172 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox172) tree172 = true := by
  simp only [tree172,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox172 1 (1568471967344827837048576987744446217274174243925712196221646383821619200000000000000000000000 : Int) false,decode_split denominator ibox172 1 (1568471967344827837048576987744446217274174243925712196221646383821619200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_173 h,accepted_180 h⟩
private noncomputable def tree171 : TapeTree := .centered (candidateRows ibox171) (candidateRows (FixedTape.midBox ibox171))
attribute [irreducible] tree171
private theorem sign_171 : 2*denominator*(computed denominator (FixedTape.midBox ibox171)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox171).gradient k).lo.natAbs ((computed denominator ibox171).gradient k).hi.natAbs : Int)*((ibox171 k).hi-(ibox171 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox171
    (computed denominator ibox171) (computed denominator (FixedTape.midBox ibox171))
    (by decide +kernel)
private theorem midpoint_even_171 : ∀ k, 2 ∣ (ibox171 k).lo+(ibox171 k).hi := by decide +kernel
private theorem accepted_171 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox171) tree171 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox171 midpoint_even_171
  simp only [tree171,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox171,candidate_valid h (FixedTape.midBox ibox171),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox171 83 (FixedTape.rowsAux denominator ibox171 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox171) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_171
private noncomputable def tree170 : TapeTree := .centered (candidateRows ibox170) (candidateRows (FixedTape.midBox ibox170))
attribute [irreducible] tree170
private theorem sign_170 : 2*denominator*(computed denominator (FixedTape.midBox ibox170)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox170).gradient k).lo.natAbs ((computed denominator ibox170).gradient k).hi.natAbs : Int)*((ibox170 k).hi-(ibox170 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox170
    (computed denominator ibox170) (computed denominator (FixedTape.midBox ibox170))
    (by decide +kernel)
private theorem midpoint_even_170 : ∀ k, 2 ∣ (ibox170 k).lo+(ibox170 k).hi := by decide +kernel
private theorem accepted_170 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox170) tree170 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox170 midpoint_even_170
  simp only [tree170,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox170,candidate_valid h (FixedTape.midBox ibox170),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox170 83 (FixedTape.rowsAux denominator ibox170 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox170) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_170
private noncomputable def tree169 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree170 tree171
attribute [irreducible] tree169
private theorem accepted_169 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox169) tree169 = true := by
  simp only [tree169,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox169 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox169 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_170 h,accepted_171 h⟩
private noncomputable def tree168 : TapeTree := .centered (candidateRows ibox168) (candidateRows (FixedTape.midBox ibox168))
attribute [irreducible] tree168
private theorem sign_168 : 2*denominator*(computed denominator (FixedTape.midBox ibox168)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox168).gradient k).lo.natAbs ((computed denominator ibox168).gradient k).hi.natAbs : Int)*((ibox168 k).hi-(ibox168 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox168
    (computed denominator ibox168) (computed denominator (FixedTape.midBox ibox168))
    (by decide +kernel)
private theorem midpoint_even_168 : ∀ k, 2 ∣ (ibox168 k).lo+(ibox168 k).hi := by decide +kernel
private theorem accepted_168 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox168) tree168 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox168 midpoint_even_168
  simp only [tree168,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox168,candidate_valid h (FixedTape.midBox ibox168),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox168 83 (FixedTape.rowsAux denominator ibox168 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox168) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_168
private noncomputable def tree167 : TapeTree := .centered (candidateRows ibox167) (candidateRows (FixedTape.midBox ibox167))
attribute [irreducible] tree167
private theorem sign_167 : 2*denominator*(computed denominator (FixedTape.midBox ibox167)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox167).gradient k).lo.natAbs ((computed denominator ibox167).gradient k).hi.natAbs : Int)*((ibox167 k).hi-(ibox167 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox167
    (computed denominator ibox167) (computed denominator (FixedTape.midBox ibox167))
    (by decide +kernel)
private theorem midpoint_even_167 : ∀ k, 2 ∣ (ibox167 k).lo+(ibox167 k).hi := by decide +kernel
private theorem accepted_167 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox167) tree167 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox167 midpoint_even_167
  simp only [tree167,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox167,candidate_valid h (FixedTape.midBox ibox167),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox167 83 (FixedTape.rowsAux denominator ibox167 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox167) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_167
private noncomputable def tree166 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree167 tree168
attribute [irreducible] tree166
private theorem accepted_166 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox166) tree166 = true := by
  simp only [tree166,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox166 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox166 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_167 h,accepted_168 h⟩
private noncomputable def tree165 : TapeTree := .split 1 (((1568471967344827837048576987744446217274174243925712196221646383821619200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree166 tree169
attribute [irreducible] tree165
private theorem accepted_165 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox165) tree165 = true := by
  simp only [tree165,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox165 1 (1568471967344827837048576987744446217274174243925712196221646383821619200000000000000000000000 : Int) false,decode_split denominator ibox165 1 (1568471967344827837048576987744446217274174243925712196221646383821619200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_166 h,accepted_169 h⟩
private noncomputable def tree164 : TapeTree := .split 2 (((1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree165 tree172
attribute [irreducible] tree164
private theorem accepted_164 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox164) tree164 = true := by
  simp only [tree164,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox164 2 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) false,decode_split denominator ibox164 2 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_165 h,accepted_172 h⟩
private noncomputable def tree163 : TapeTree := .split 1 (((1622557207598097762464045159735634017869835424750736754712047983263744000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree164 tree187
attribute [irreducible] tree163
private theorem accepted_163 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox163) tree163 = true := by
  simp only [tree163,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox163 1 (1622557207598097762464045159735634017869835424750736754712047983263744000000000000000000000000 : Int) false,decode_split denominator ibox163 1 (1622557207598097762464045159735634017869835424750736754712047983263744000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_164 h,accepted_187 h⟩
private noncomputable def tree162 : TapeTree := .centered (candidateRows ibox162) (candidateRows (FixedTape.midBox ibox162))
attribute [irreducible] tree162
private theorem sign_162 : 2*denominator*(computed denominator (FixedTape.midBox ibox162)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox162).gradient k).lo.natAbs ((computed denominator ibox162).gradient k).hi.natAbs : Int)*((ibox162 k).hi-(ibox162 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox162
    (computed denominator ibox162) (computed denominator (FixedTape.midBox ibox162))
    (by decide +kernel)
private theorem midpoint_even_162 : ∀ k, 2 ∣ (ibox162 k).lo+(ibox162 k).hi := by decide +kernel
private theorem accepted_162 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox162) tree162 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox162 midpoint_even_162
  simp only [tree162,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox162,candidate_valid h (FixedTape.midBox ibox162),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox162 83 (FixedTape.rowsAux denominator ibox162 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox162) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_162
private noncomputable def tree161 : TapeTree := .centered (candidateRows ibox161) (candidateRows (FixedTape.midBox ibox161))
attribute [irreducible] tree161
private theorem sign_161 : 2*denominator*(computed denominator (FixedTape.midBox ibox161)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox161).gradient k).lo.natAbs ((computed denominator ibox161).gradient k).hi.natAbs : Int)*((ibox161 k).hi-(ibox161 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox161
    (computed denominator ibox161) (computed denominator (FixedTape.midBox ibox161))
    (by decide +kernel)
private theorem midpoint_even_161 : ∀ k, 2 ∣ (ibox161 k).lo+(ibox161 k).hi := by decide +kernel
private theorem accepted_161 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox161) tree161 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox161 midpoint_even_161
  simp only [tree161,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox161,candidate_valid h (FixedTape.midBox ibox161),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox161 83 (FixedTape.rowsAux denominator ibox161 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox161) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_161
private noncomputable def tree160 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree161 tree162
attribute [irreducible] tree160
private theorem accepted_160 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox160) tree160 = true := by
  simp only [tree160,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox160 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox160 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_161 h,accepted_162 h⟩
private noncomputable def tree159 : TapeTree := .centered (candidateRows ibox159) (candidateRows (FixedTape.midBox ibox159))
attribute [irreducible] tree159
private theorem sign_159 : 2*denominator*(computed denominator (FixedTape.midBox ibox159)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox159).gradient k).lo.natAbs ((computed denominator ibox159).gradient k).hi.natAbs : Int)*((ibox159 k).hi-(ibox159 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox159
    (computed denominator ibox159) (computed denominator (FixedTape.midBox ibox159))
    (by decide +kernel)
private theorem midpoint_even_159 : ∀ k, 2 ∣ (ibox159 k).lo+(ibox159 k).hi := by decide +kernel
private theorem accepted_159 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox159) tree159 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox159 midpoint_even_159
  simp only [tree159,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox159,candidate_valid h (FixedTape.midBox ibox159),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox159 83 (FixedTape.rowsAux denominator ibox159 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox159) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_159
private noncomputable def tree158 : TapeTree := .centered (candidateRows ibox158) (candidateRows (FixedTape.midBox ibox158))
attribute [irreducible] tree158
private theorem sign_158 : 2*denominator*(computed denominator (FixedTape.midBox ibox158)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox158).gradient k).lo.natAbs ((computed denominator ibox158).gradient k).hi.natAbs : Int)*((ibox158 k).hi-(ibox158 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox158
    (computed denominator ibox158) (computed denominator (FixedTape.midBox ibox158))
    (by decide +kernel)
private theorem midpoint_even_158 : ∀ k, 2 ∣ (ibox158 k).lo+(ibox158 k).hi := by decide +kernel
private theorem accepted_158 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox158) tree158 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox158 midpoint_even_158
  simp only [tree158,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox158,candidate_valid h (FixedTape.midBox ibox158),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox158 83 (FixedTape.rowsAux denominator ibox158 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox158) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_158
private noncomputable def tree157 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree158 tree159
attribute [irreducible] tree157
private theorem accepted_157 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox157) tree157 = true := by
  simp only [tree157,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox157 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox157 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_158 h,accepted_159 h⟩
private noncomputable def tree156 : TapeTree := .split 1 (((1676642447851367687879513331726821818465496605575761313202449582705868800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree157 tree160
attribute [irreducible] tree156
private theorem accepted_156 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox156) tree156 = true := by
  simp only [tree156,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox156 1 (1676642447851367687879513331726821818465496605575761313202449582705868800000000000000000000000 : Int) false,decode_split denominator ibox156 1 (1676642447851367687879513331726821818465496605575761313202449582705868800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_157 h,accepted_160 h⟩
private noncomputable def tree155 : TapeTree := .centered (candidateRows ibox155) (candidateRows (FixedTape.midBox ibox155))
attribute [irreducible] tree155
private theorem sign_155 : 2*denominator*(computed denominator (FixedTape.midBox ibox155)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox155).gradient k).lo.natAbs ((computed denominator ibox155).gradient k).hi.natAbs : Int)*((ibox155 k).hi-(ibox155 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox155
    (computed denominator ibox155) (computed denominator (FixedTape.midBox ibox155))
    (by decide +kernel)
private theorem midpoint_even_155 : ∀ k, 2 ∣ (ibox155 k).lo+(ibox155 k).hi := by decide +kernel
private theorem accepted_155 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox155) tree155 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox155 midpoint_even_155
  simp only [tree155,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox155,candidate_valid h (FixedTape.midBox ibox155),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox155 83 (FixedTape.rowsAux denominator ibox155 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox155) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_155
private noncomputable def tree154 : TapeTree := .centered (candidateRows ibox154) (candidateRows (FixedTape.midBox ibox154))
attribute [irreducible] tree154
private theorem sign_154 : 2*denominator*(computed denominator (FixedTape.midBox ibox154)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox154).gradient k).lo.natAbs ((computed denominator ibox154).gradient k).hi.natAbs : Int)*((ibox154 k).hi-(ibox154 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox154
    (computed denominator ibox154) (computed denominator (FixedTape.midBox ibox154))
    (by decide +kernel)
private theorem midpoint_even_154 : ∀ k, 2 ∣ (ibox154 k).lo+(ibox154 k).hi := by decide +kernel
private theorem accepted_154 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox154) tree154 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox154 midpoint_even_154
  simp only [tree154,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox154,candidate_valid h (FixedTape.midBox ibox154),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox154 83 (FixedTape.rowsAux denominator ibox154 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox154) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_154
private noncomputable def tree153 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree154 tree155
attribute [irreducible] tree153
private theorem accepted_153 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox153) tree153 = true := by
  simp only [tree153,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox153 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox153 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_154 h,accepted_155 h⟩
private noncomputable def tree152 : TapeTree := .centered (candidateRows ibox152) (candidateRows (FixedTape.midBox ibox152))
attribute [irreducible] tree152
private theorem sign_152 : 2*denominator*(computed denominator (FixedTape.midBox ibox152)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox152).gradient k).lo.natAbs ((computed denominator ibox152).gradient k).hi.natAbs : Int)*((ibox152 k).hi-(ibox152 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox152
    (computed denominator ibox152) (computed denominator (FixedTape.midBox ibox152))
    (by decide +kernel)
private theorem midpoint_even_152 : ∀ k, 2 ∣ (ibox152 k).lo+(ibox152 k).hi := by decide +kernel
private theorem accepted_152 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox152) tree152 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox152 midpoint_even_152
  simp only [tree152,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox152,candidate_valid h (FixedTape.midBox ibox152),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox152 83 (FixedTape.rowsAux denominator ibox152 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox152) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_152
private noncomputable def tree151 : TapeTree := .centered (candidateRows ibox151) (candidateRows (FixedTape.midBox ibox151))
attribute [irreducible] tree151
private theorem sign_151 : 2*denominator*(computed denominator (FixedTape.midBox ibox151)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox151).gradient k).lo.natAbs ((computed denominator ibox151).gradient k).hi.natAbs : Int)*((ibox151 k).hi-(ibox151 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox151
    (computed denominator ibox151) (computed denominator (FixedTape.midBox ibox151))
    (by decide +kernel)
private theorem midpoint_even_151 : ∀ k, 2 ∣ (ibox151 k).lo+(ibox151 k).hi := by decide +kernel
private theorem accepted_151 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox151) tree151 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox151 midpoint_even_151
  simp only [tree151,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox151,candidate_valid h (FixedTape.midBox ibox151),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox151 83 (FixedTape.rowsAux denominator ibox151 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox151) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_151
private noncomputable def tree150 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree151 tree152
attribute [irreducible] tree150
private theorem accepted_150 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox150) tree150 = true := by
  simp only [tree150,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox150 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox150 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_151 h,accepted_152 h⟩
private noncomputable def tree149 : TapeTree := .split 1 (((1568471967344827837048576987744446217274174243925712196221646383821619200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree150 tree153
attribute [irreducible] tree149
private theorem accepted_149 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox149) tree149 = true := by
  simp only [tree149,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox149 1 (1568471967344827837048576987744446217274174243925712196221646383821619200000000000000000000000 : Int) false,decode_split denominator ibox149 1 (1568471967344827837048576987744446217274174243925712196221646383821619200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_150 h,accepted_153 h⟩
private noncomputable def tree148 : TapeTree := .split 1 (((1622557207598097762464045159735634017869835424750736754712047983263744000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree149 tree156
attribute [irreducible] tree148
private theorem accepted_148 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox148) tree148 = true := by
  simp only [tree148,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox148 1 (1622557207598097762464045159735634017869835424750736754712047983263744000000000000000000000000 : Int) false,decode_split denominator ibox148 1 (1622557207598097762464045159735634017869835424750736754712047983263744000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_149 h,accepted_156 h⟩
private noncomputable def tree147 : TapeTree := .split 2 (((865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree148 tree163
attribute [irreducible] tree147
private theorem accepted_147 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox147) tree147 = true := by
  simp only [tree147,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox147 2 (865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) false,decode_split denominator ibox147 2 (865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_148 h,accepted_163 h⟩
private noncomputable def tree146 : TapeTree := .centered (candidateRows ibox146) (candidateRows (FixedTape.midBox ibox146))
attribute [irreducible] tree146
private theorem sign_146 : 2*denominator*(computed denominator (FixedTape.midBox ibox146)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox146).gradient k).lo.natAbs ((computed denominator ibox146).gradient k).hi.natAbs : Int)*((ibox146 k).hi-(ibox146 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox146
    (computed denominator ibox146) (computed denominator (FixedTape.midBox ibox146))
    (by decide +kernel)
private theorem midpoint_even_146 : ∀ k, 2 ∣ (ibox146 k).lo+(ibox146 k).hi := by decide +kernel
private theorem accepted_146 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox146) tree146 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox146 midpoint_even_146
  simp only [tree146,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox146,candidate_valid h (FixedTape.midBox ibox146),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox146 83 (FixedTape.rowsAux denominator ibox146 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox146) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_146
private noncomputable def tree145 : TapeTree := .centered (candidateRows ibox145) (candidateRows (FixedTape.midBox ibox145))
attribute [irreducible] tree145
private theorem sign_145 : 2*denominator*(computed denominator (FixedTape.midBox ibox145)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox145).gradient k).lo.natAbs ((computed denominator ibox145).gradient k).hi.natAbs : Int)*((ibox145 k).hi-(ibox145 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox145
    (computed denominator ibox145) (computed denominator (FixedTape.midBox ibox145))
    (by decide +kernel)
private theorem midpoint_even_145 : ∀ k, 2 ∣ (ibox145 k).lo+(ibox145 k).hi := by decide +kernel
private theorem accepted_145 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox145) tree145 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox145 midpoint_even_145
  simp only [tree145,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox145,candidate_valid h (FixedTape.midBox ibox145),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox145 83 (FixedTape.rowsAux denominator ibox145 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox145) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_145
private noncomputable def tree144 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree145 tree146
attribute [irreducible] tree144
private theorem accepted_144 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox144) tree144 = true := by
  simp only [tree144,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox144 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox144 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_145 h,accepted_146 h⟩
private noncomputable def tree143 : TapeTree := .centered (candidateRows ibox143) (candidateRows (FixedTape.midBox ibox143))
attribute [irreducible] tree143
private theorem sign_143 : 2*denominator*(computed denominator (FixedTape.midBox ibox143)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox143).gradient k).lo.natAbs ((computed denominator ibox143).gradient k).hi.natAbs : Int)*((ibox143 k).hi-(ibox143 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox143
    (computed denominator ibox143) (computed denominator (FixedTape.midBox ibox143))
    (by decide +kernel)
private theorem midpoint_even_143 : ∀ k, 2 ∣ (ibox143 k).lo+(ibox143 k).hi := by decide +kernel
private theorem accepted_143 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox143) tree143 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox143 midpoint_even_143
  simp only [tree143,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox143,candidate_valid h (FixedTape.midBox ibox143),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox143 83 (FixedTape.rowsAux denominator ibox143 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox143) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_143
private noncomputable def tree142 : TapeTree := .centered (candidateRows ibox142) (candidateRows (FixedTape.midBox ibox142))
attribute [irreducible] tree142
private theorem sign_142 : 2*denominator*(computed denominator (FixedTape.midBox ibox142)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox142).gradient k).lo.natAbs ((computed denominator ibox142).gradient k).hi.natAbs : Int)*((ibox142 k).hi-(ibox142 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox142
    (computed denominator ibox142) (computed denominator (FixedTape.midBox ibox142))
    (by decide +kernel)
private theorem midpoint_even_142 : ∀ k, 2 ∣ (ibox142 k).lo+(ibox142 k).hi := by decide +kernel
private theorem accepted_142 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox142) tree142 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox142 midpoint_even_142
  simp only [tree142,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox142,candidate_valid h (FixedTape.midBox ibox142),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox142 83 (FixedTape.rowsAux denominator ibox142 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox142) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_142
private noncomputable def tree141 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree142 tree143
attribute [irreducible] tree141
private theorem accepted_141 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox141) tree141 = true := by
  simp only [tree141,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox141 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox141 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_142 h,accepted_143 h⟩
private noncomputable def tree140 : TapeTree := .split 2 (((1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree141 tree144
attribute [irreducible] tree140
private theorem accepted_140 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox140) tree140 = true := by
  simp only [tree140,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox140 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) false,decode_split denominator ibox140 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_141 h,accepted_144 h⟩
private noncomputable def tree139 : TapeTree := .centered (candidateRows ibox139) (candidateRows (FixedTape.midBox ibox139))
attribute [irreducible] tree139
private theorem sign_139 : 2*denominator*(computed denominator (FixedTape.midBox ibox139)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox139).gradient k).lo.natAbs ((computed denominator ibox139).gradient k).hi.natAbs : Int)*((ibox139 k).hi-(ibox139 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox139
    (computed denominator ibox139) (computed denominator (FixedTape.midBox ibox139))
    (by decide +kernel)
private theorem midpoint_even_139 : ∀ k, 2 ∣ (ibox139 k).lo+(ibox139 k).hi := by decide +kernel
private theorem accepted_139 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox139) tree139 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox139 midpoint_even_139
  simp only [tree139,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox139,candidate_valid h (FixedTape.midBox ibox139),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox139 83 (FixedTape.rowsAux denominator ibox139 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox139) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_139
private noncomputable def tree138 : TapeTree := .centered (candidateRows ibox138) (candidateRows (FixedTape.midBox ibox138))
attribute [irreducible] tree138
private theorem sign_138 : 2*denominator*(computed denominator (FixedTape.midBox ibox138)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox138).gradient k).lo.natAbs ((computed denominator ibox138).gradient k).hi.natAbs : Int)*((ibox138 k).hi-(ibox138 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox138
    (computed denominator ibox138) (computed denominator (FixedTape.midBox ibox138))
    (by decide +kernel)
private theorem midpoint_even_138 : ∀ k, 2 ∣ (ibox138 k).lo+(ibox138 k).hi := by decide +kernel
private theorem accepted_138 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox138) tree138 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox138 midpoint_even_138
  simp only [tree138,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox138,candidate_valid h (FixedTape.midBox ibox138),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox138 83 (FixedTape.rowsAux denominator ibox138 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox138) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_138
private noncomputable def tree137 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree138 tree139
attribute [irreducible] tree137
private theorem accepted_137 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox137) tree137 = true := by
  simp only [tree137,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox137 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox137 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_138 h,accepted_139 h⟩
private noncomputable def tree136 : TapeTree := .centered (candidateRows ibox136) (candidateRows (FixedTape.midBox ibox136))
attribute [irreducible] tree136
private theorem sign_136 : 2*denominator*(computed denominator (FixedTape.midBox ibox136)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox136).gradient k).lo.natAbs ((computed denominator ibox136).gradient k).hi.natAbs : Int)*((ibox136 k).hi-(ibox136 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox136
    (computed denominator ibox136) (computed denominator (FixedTape.midBox ibox136))
    (by decide +kernel)
private theorem midpoint_even_136 : ∀ k, 2 ∣ (ibox136 k).lo+(ibox136 k).hi := by decide +kernel
private theorem accepted_136 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox136) tree136 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox136 midpoint_even_136
  simp only [tree136,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox136,candidate_valid h (FixedTape.midBox ibox136),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox136 83 (FixedTape.rowsAux denominator ibox136 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox136) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_136
private noncomputable def tree135 : TapeTree := .centered (candidateRows ibox135) (candidateRows (FixedTape.midBox ibox135))
attribute [irreducible] tree135
private theorem sign_135 : 2*denominator*(computed denominator (FixedTape.midBox ibox135)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox135).gradient k).lo.natAbs ((computed denominator ibox135).gradient k).hi.natAbs : Int)*((ibox135 k).hi-(ibox135 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox135
    (computed denominator ibox135) (computed denominator (FixedTape.midBox ibox135))
    (by decide +kernel)
private theorem midpoint_even_135 : ∀ k, 2 ∣ (ibox135 k).lo+(ibox135 k).hi := by decide +kernel
private theorem accepted_135 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox135) tree135 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox135 midpoint_even_135
  simp only [tree135,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox135,candidate_valid h (FixedTape.midBox ibox135),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox135 83 (FixedTape.rowsAux denominator ibox135 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox135) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_135
private noncomputable def tree134 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree135 tree136
attribute [irreducible] tree134
private theorem accepted_134 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox134) tree134 = true := by
  simp only [tree134,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox134 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox134 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_135 h,accepted_136 h⟩
private noncomputable def tree133 : TapeTree := .split 2 (((1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree134 tree137
attribute [irreducible] tree133
private theorem accepted_133 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox133) tree133 = true := by
  simp only [tree133,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox133 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) false,decode_split denominator ibox133 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_134 h,accepted_137 h⟩
private noncomputable def tree132 : TapeTree := .split 1 (((1460301486838287986217640643762070616082851882275663079240843184937369600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree133 tree140
attribute [irreducible] tree132
private theorem accepted_132 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox132) tree132 = true := by
  simp only [tree132,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox132 1 (1460301486838287986217640643762070616082851882275663079240843184937369600000000000000000000000 : Int) false,decode_split denominator ibox132 1 (1460301486838287986217640643762070616082851882275663079240843184937369600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_133 h,accepted_140 h⟩
private noncomputable def tree131 : TapeTree := .centered (candidateRows ibox131) (candidateRows (FixedTape.midBox ibox131))
attribute [irreducible] tree131
private theorem sign_131 : 2*denominator*(computed denominator (FixedTape.midBox ibox131)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox131).gradient k).lo.natAbs ((computed denominator ibox131).gradient k).hi.natAbs : Int)*((ibox131 k).hi-(ibox131 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox131
    (computed denominator ibox131) (computed denominator (FixedTape.midBox ibox131))
    (by decide +kernel)
private theorem midpoint_even_131 : ∀ k, 2 ∣ (ibox131 k).lo+(ibox131 k).hi := by decide +kernel
private theorem accepted_131 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox131) tree131 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox131 midpoint_even_131
  simp only [tree131,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox131,candidate_valid h (FixedTape.midBox ibox131),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox131 83 (FixedTape.rowsAux denominator ibox131 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox131) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_131
private noncomputable def tree130 : TapeTree := .centered (candidateRows ibox130) (candidateRows (FixedTape.midBox ibox130))
attribute [irreducible] tree130
private theorem sign_130 : 2*denominator*(computed denominator (FixedTape.midBox ibox130)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox130).gradient k).lo.natAbs ((computed denominator ibox130).gradient k).hi.natAbs : Int)*((ibox130 k).hi-(ibox130 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox130
    (computed denominator ibox130) (computed denominator (FixedTape.midBox ibox130))
    (by decide +kernel)
private theorem midpoint_even_130 : ∀ k, 2 ∣ (ibox130 k).lo+(ibox130 k).hi := by decide +kernel
private theorem accepted_130 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox130) tree130 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox130 midpoint_even_130
  simp only [tree130,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox130,candidate_valid h (FixedTape.midBox ibox130),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox130 83 (FixedTape.rowsAux denominator ibox130 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox130) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_130
private noncomputable def tree129 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree130 tree131
attribute [irreducible] tree129
private theorem accepted_129 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox129) tree129 = true := by
  simp only [tree129,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox129 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox129 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_130 h,accepted_131 h⟩
private noncomputable def tree128 : TapeTree := .centered (candidateRows ibox128) (candidateRows (FixedTape.midBox ibox128))
attribute [irreducible] tree128
private theorem sign_128 : 2*denominator*(computed denominator (FixedTape.midBox ibox128)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox128).gradient k).lo.natAbs ((computed denominator ibox128).gradient k).hi.natAbs : Int)*((ibox128 k).hi-(ibox128 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox128
    (computed denominator ibox128) (computed denominator (FixedTape.midBox ibox128))
    (by decide +kernel)
private theorem midpoint_even_128 : ∀ k, 2 ∣ (ibox128 k).lo+(ibox128 k).hi := by decide +kernel
private theorem accepted_128 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox128) tree128 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox128 midpoint_even_128
  simp only [tree128,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox128,candidate_valid h (FixedTape.midBox ibox128),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox128 83 (FixedTape.rowsAux denominator ibox128 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox128) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_128
private noncomputable def tree127 : TapeTree := .split 1 (((1460301486838287986217640643762070616082851882275663079240843184937369600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree128 tree129
attribute [irreducible] tree127
private theorem accepted_127 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox127) tree127 = true := by
  simp only [tree127,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox127 1 (1460301486838287986217640643762070616082851882275663079240843184937369600000000000000000000000 : Int) false,decode_split denominator ibox127 1 (1460301486838287986217640643762070616082851882275663079240843184937369600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_128 h,accepted_129 h⟩
private noncomputable def tree126 : TapeTree := .split 2 (((1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree127 tree132
attribute [irreducible] tree126
private theorem accepted_126 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox126) tree126 = true := by
  simp only [tree126,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox126 2 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) false,decode_split denominator ibox126 2 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_127 h,accepted_132 h⟩
private noncomputable def tree125 : TapeTree := .centered (candidateRows ibox125) (candidateRows (FixedTape.midBox ibox125))
attribute [irreducible] tree125
private theorem sign_125 : 2*denominator*(computed denominator (FixedTape.midBox ibox125)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox125).gradient k).lo.natAbs ((computed denominator ibox125).gradient k).hi.natAbs : Int)*((ibox125 k).hi-(ibox125 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox125
    (computed denominator ibox125) (computed denominator (FixedTape.midBox ibox125))
    (by decide +kernel)
private theorem midpoint_even_125 : ∀ k, 2 ∣ (ibox125 k).lo+(ibox125 k).hi := by decide +kernel
private theorem accepted_125 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox125) tree125 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox125 midpoint_even_125
  simp only [tree125,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox125,candidate_valid h (FixedTape.midBox ibox125),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox125 83 (FixedTape.rowsAux denominator ibox125 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox125) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_125
private noncomputable def tree124 : TapeTree := .centered (candidateRows ibox124) (candidateRows (FixedTape.midBox ibox124))
attribute [irreducible] tree124
private theorem sign_124 : 2*denominator*(computed denominator (FixedTape.midBox ibox124)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox124).gradient k).lo.natAbs ((computed denominator ibox124).gradient k).hi.natAbs : Int)*((ibox124 k).hi-(ibox124 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox124
    (computed denominator ibox124) (computed denominator (FixedTape.midBox ibox124))
    (by decide +kernel)
private theorem midpoint_even_124 : ∀ k, 2 ∣ (ibox124 k).lo+(ibox124 k).hi := by decide +kernel
private theorem accepted_124 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox124) tree124 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox124 midpoint_even_124
  simp only [tree124,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox124,candidate_valid h (FixedTape.midBox ibox124),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox124 83 (FixedTape.rowsAux denominator ibox124 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox124) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_124
private noncomputable def tree123 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree124 tree125
attribute [irreducible] tree123
private theorem accepted_123 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox123) tree123 = true := by
  simp only [tree123,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox123 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox123 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_124 h,accepted_125 h⟩
private noncomputable def tree122 : TapeTree := .centered (candidateRows ibox122) (candidateRows (FixedTape.midBox ibox122))
attribute [irreducible] tree122
private theorem sign_122 : 2*denominator*(computed denominator (FixedTape.midBox ibox122)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox122).gradient k).lo.natAbs ((computed denominator ibox122).gradient k).hi.natAbs : Int)*((ibox122 k).hi-(ibox122 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox122
    (computed denominator ibox122) (computed denominator (FixedTape.midBox ibox122))
    (by decide +kernel)
private theorem midpoint_even_122 : ∀ k, 2 ∣ (ibox122 k).lo+(ibox122 k).hi := by decide +kernel
private theorem accepted_122 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox122) tree122 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox122 midpoint_even_122
  simp only [tree122,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox122,candidate_valid h (FixedTape.midBox ibox122),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox122 83 (FixedTape.rowsAux denominator ibox122 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox122) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_122
private noncomputable def tree121 : TapeTree := .split 2 (((1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree122 tree123
attribute [irreducible] tree121
private theorem accepted_121 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox121) tree121 = true := by
  simp only [tree121,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox121 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) false,decode_split denominator ibox121 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_122 h,accepted_123 h⟩
private noncomputable def tree120 : TapeTree := .centered (candidateRows ibox120) (candidateRows (FixedTape.midBox ibox120))
attribute [irreducible] tree120
private theorem sign_120 : 2*denominator*(computed denominator (FixedTape.midBox ibox120)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox120).gradient k).lo.natAbs ((computed denominator ibox120).gradient k).hi.natAbs : Int)*((ibox120 k).hi-(ibox120 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox120
    (computed denominator ibox120) (computed denominator (FixedTape.midBox ibox120))
    (by decide +kernel)
private theorem midpoint_even_120 : ∀ k, 2 ∣ (ibox120 k).lo+(ibox120 k).hi := by decide +kernel
private theorem accepted_120 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox120) tree120 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox120 midpoint_even_120
  simp only [tree120,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox120,candidate_valid h (FixedTape.midBox ibox120),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox120 83 (FixedTape.rowsAux denominator ibox120 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox120) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_120
private noncomputable def tree119 : TapeTree := .centered (candidateRows ibox119) (candidateRows (FixedTape.midBox ibox119))
attribute [irreducible] tree119
private theorem sign_119 : 2*denominator*(computed denominator (FixedTape.midBox ibox119)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox119).gradient k).lo.natAbs ((computed denominator ibox119).gradient k).hi.natAbs : Int)*((ibox119 k).hi-(ibox119 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox119
    (computed denominator ibox119) (computed denominator (FixedTape.midBox ibox119))
    (by decide +kernel)
private theorem midpoint_even_119 : ∀ k, 2 ∣ (ibox119 k).lo+(ibox119 k).hi := by decide +kernel
private theorem accepted_119 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox119) tree119 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox119 midpoint_even_119
  simp only [tree119,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox119,candidate_valid h (FixedTape.midBox ibox119),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox119 83 (FixedTape.rowsAux denominator ibox119 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox119) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_119
private noncomputable def tree118 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree119 tree120
attribute [irreducible] tree118
private theorem accepted_118 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox118) tree118 = true := by
  simp only [tree118,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox118 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox118 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_119 h,accepted_120 h⟩
private noncomputable def tree117 : TapeTree := .centered (candidateRows ibox117) (candidateRows (FixedTape.midBox ibox117))
attribute [irreducible] tree117
private theorem sign_117 : 2*denominator*(computed denominator (FixedTape.midBox ibox117)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox117).gradient k).lo.natAbs ((computed denominator ibox117).gradient k).hi.natAbs : Int)*((ibox117 k).hi-(ibox117 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox117
    (computed denominator ibox117) (computed denominator (FixedTape.midBox ibox117))
    (by decide +kernel)
private theorem midpoint_even_117 : ∀ k, 2 ∣ (ibox117 k).lo+(ibox117 k).hi := by decide +kernel
private theorem accepted_117 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox117) tree117 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox117 midpoint_even_117
  simp only [tree117,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox117,candidate_valid h (FixedTape.midBox ibox117),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox117 83 (FixedTape.rowsAux denominator ibox117 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox117) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_117
private noncomputable def tree116 : TapeTree := .split 2 (((1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree117 tree118
attribute [irreducible] tree116
private theorem accepted_116 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox116) tree116 = true := by
  simp only [tree116,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox116 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) false,decode_split denominator ibox116 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_117 h,accepted_118 h⟩
private noncomputable def tree115 : TapeTree := .split 1 (((1352131006331748135386704299779695014891529520625613962260039986053120000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree116 tree121
attribute [irreducible] tree115
private theorem accepted_115 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox115) tree115 = true := by
  simp only [tree115,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox115 1 (1352131006331748135386704299779695014891529520625613962260039986053120000000000000000000000000 : Int) false,decode_split denominator ibox115 1 (1352131006331748135386704299779695014891529520625613962260039986053120000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_116 h,accepted_121 h⟩
private noncomputable def tree114 : TapeTree := .centered (candidateRows ibox114) (candidateRows (FixedTape.midBox ibox114))
attribute [irreducible] tree114
private theorem sign_114 : 2*denominator*(computed denominator (FixedTape.midBox ibox114)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox114).gradient k).lo.natAbs ((computed denominator ibox114).gradient k).hi.natAbs : Int)*((ibox114 k).hi-(ibox114 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox114
    (computed denominator ibox114) (computed denominator (FixedTape.midBox ibox114))
    (by decide +kernel)
private theorem midpoint_even_114 : ∀ k, 2 ∣ (ibox114 k).lo+(ibox114 k).hi := by decide +kernel
private theorem accepted_114 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox114) tree114 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox114 midpoint_even_114
  simp only [tree114,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox114,candidate_valid h (FixedTape.midBox ibox114),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox114 83 (FixedTape.rowsAux denominator ibox114 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox114) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_114
private noncomputable def tree113 : TapeTree := .centered (candidateRows ibox113) (candidateRows (FixedTape.midBox ibox113))
attribute [irreducible] tree113
private theorem sign_113 : 2*denominator*(computed denominator (FixedTape.midBox ibox113)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox113).gradient k).lo.natAbs ((computed denominator ibox113).gradient k).hi.natAbs : Int)*((ibox113 k).hi-(ibox113 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox113
    (computed denominator ibox113) (computed denominator (FixedTape.midBox ibox113))
    (by decide +kernel)
private theorem midpoint_even_113 : ∀ k, 2 ∣ (ibox113 k).lo+(ibox113 k).hi := by decide +kernel
private theorem accepted_113 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox113) tree113 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox113 midpoint_even_113
  simp only [tree113,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox113,candidate_valid h (FixedTape.midBox ibox113),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox113 83 (FixedTape.rowsAux denominator ibox113 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox113) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_113
private noncomputable def tree112 : TapeTree := .split 1 (((1352131006331748135386704299779695014891529520625613962260039986053120000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree113 tree114
attribute [irreducible] tree112
private theorem accepted_112 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox112) tree112 = true := by
  simp only [tree112,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox112 1 (1352131006331748135386704299779695014891529520625613962260039986053120000000000000000000000000 : Int) false,decode_split denominator ibox112 1 (1352131006331748135386704299779695014891529520625613962260039986053120000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_113 h,accepted_114 h⟩
private noncomputable def tree111 : TapeTree := .split 2 (((1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree112 tree115
attribute [irreducible] tree111
private theorem accepted_111 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox111) tree111 = true := by
  simp only [tree111,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox111 2 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) false,decode_split denominator ibox111 2 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_112 h,accepted_115 h⟩
private noncomputable def tree110 : TapeTree := .split 1 (((1406216246585018060802172471770882815487190701450638520750441585495244800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree111 tree126
attribute [irreducible] tree110
private theorem accepted_110 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox110) tree110 = true := by
  simp only [tree110,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox110 1 (1406216246585018060802172471770882815487190701450638520750441585495244800000000000000000000000 : Int) false,decode_split denominator ibox110 1 (1406216246585018060802172471770882815487190701450638520750441585495244800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_111 h,accepted_126 h⟩
private noncomputable def tree109 : TapeTree := .centered (candidateRows ibox109) (candidateRows (FixedTape.midBox ibox109))
attribute [irreducible] tree109
private theorem sign_109 : 2*denominator*(computed denominator (FixedTape.midBox ibox109)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox109).gradient k).lo.natAbs ((computed denominator ibox109).gradient k).hi.natAbs : Int)*((ibox109 k).hi-(ibox109 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox109
    (computed denominator ibox109) (computed denominator (FixedTape.midBox ibox109))
    (by decide +kernel)
private theorem midpoint_even_109 : ∀ k, 2 ∣ (ibox109 k).lo+(ibox109 k).hi := by decide +kernel
private theorem accepted_109 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox109) tree109 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox109 midpoint_even_109
  simp only [tree109,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox109,candidate_valid h (FixedTape.midBox ibox109),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox109 83 (FixedTape.rowsAux denominator ibox109 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox109) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_109
private noncomputable def tree108 : TapeTree := .centered (candidateRows ibox108) (candidateRows (FixedTape.midBox ibox108))
attribute [irreducible] tree108
private theorem sign_108 : 2*denominator*(computed denominator (FixedTape.midBox ibox108)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox108).gradient k).lo.natAbs ((computed denominator ibox108).gradient k).hi.natAbs : Int)*((ibox108 k).hi-(ibox108 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox108
    (computed denominator ibox108) (computed denominator (FixedTape.midBox ibox108))
    (by decide +kernel)
private theorem midpoint_even_108 : ∀ k, 2 ∣ (ibox108 k).lo+(ibox108 k).hi := by decide +kernel
private theorem accepted_108 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox108) tree108 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox108 midpoint_even_108
  simp only [tree108,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox108,candidate_valid h (FixedTape.midBox ibox108),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox108 83 (FixedTape.rowsAux denominator ibox108 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox108) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_108
private noncomputable def tree107 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree108 tree109
attribute [irreducible] tree107
private theorem accepted_107 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox107) tree107 = true := by
  simp only [tree107,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox107 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox107 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_108 h,accepted_109 h⟩
private noncomputable def tree106 : TapeTree := .centered (candidateRows ibox106) (candidateRows (FixedTape.midBox ibox106))
attribute [irreducible] tree106
private theorem sign_106 : 2*denominator*(computed denominator (FixedTape.midBox ibox106)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox106).gradient k).lo.natAbs ((computed denominator ibox106).gradient k).hi.natAbs : Int)*((ibox106 k).hi-(ibox106 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox106
    (computed denominator ibox106) (computed denominator (FixedTape.midBox ibox106))
    (by decide +kernel)
private theorem midpoint_even_106 : ∀ k, 2 ∣ (ibox106 k).lo+(ibox106 k).hi := by decide +kernel
private theorem accepted_106 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox106) tree106 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox106 midpoint_even_106
  simp only [tree106,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox106,candidate_valid h (FixedTape.midBox ibox106),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox106 83 (FixedTape.rowsAux denominator ibox106 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox106) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_106
private noncomputable def tree105 : TapeTree := .split 1 (((1460301486838287986217640643762070616082851882275663079240843184937369600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree106 tree107
attribute [irreducible] tree105
private theorem accepted_105 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox105) tree105 = true := by
  simp only [tree105,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox105 1 (1460301486838287986217640643762070616082851882275663079240843184937369600000000000000000000000 : Int) false,decode_split denominator ibox105 1 (1460301486838287986217640643762070616082851882275663079240843184937369600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_106 h,accepted_107 h⟩
private noncomputable def tree104 : TapeTree := .centered (candidateRows ibox104) (candidateRows (FixedTape.midBox ibox104))
attribute [irreducible] tree104
private theorem sign_104 : 2*denominator*(computed denominator (FixedTape.midBox ibox104)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox104).gradient k).lo.natAbs ((computed denominator ibox104).gradient k).hi.natAbs : Int)*((ibox104 k).hi-(ibox104 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox104
    (computed denominator ibox104) (computed denominator (FixedTape.midBox ibox104))
    (by decide +kernel)
private theorem midpoint_even_104 : ∀ k, 2 ∣ (ibox104 k).lo+(ibox104 k).hi := by decide +kernel
private theorem accepted_104 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox104) tree104 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox104 midpoint_even_104
  simp only [tree104,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox104,candidate_valid h (FixedTape.midBox ibox104),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox104 83 (FixedTape.rowsAux denominator ibox104 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox104) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_104
private noncomputable def tree103 : TapeTree := .centered (candidateRows ibox103) (candidateRows (FixedTape.midBox ibox103))
attribute [irreducible] tree103
private theorem sign_103 : 2*denominator*(computed denominator (FixedTape.midBox ibox103)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox103).gradient k).lo.natAbs ((computed denominator ibox103).gradient k).hi.natAbs : Int)*((ibox103 k).hi-(ibox103 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox103
    (computed denominator ibox103) (computed denominator (FixedTape.midBox ibox103))
    (by decide +kernel)
private theorem midpoint_even_103 : ∀ k, 2 ∣ (ibox103 k).lo+(ibox103 k).hi := by decide +kernel
private theorem accepted_103 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox103) tree103 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox103 midpoint_even_103
  simp only [tree103,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox103,candidate_valid h (FixedTape.midBox ibox103),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox103 83 (FixedTape.rowsAux denominator ibox103 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox103) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_103
private noncomputable def tree102 : TapeTree := .split 1 (((1352131006331748135386704299779695014891529520625613962260039986053120000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree103 tree104
attribute [irreducible] tree102
private theorem accepted_102 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox102) tree102 = true := by
  simp only [tree102,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox102 1 (1352131006331748135386704299779695014891529520625613962260039986053120000000000000000000000000 : Int) false,decode_split denominator ibox102 1 (1352131006331748135386704299779695014891529520625613962260039986053120000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_103 h,accepted_104 h⟩
private noncomputable def tree101 : TapeTree := .split 1 (((1406216246585018060802172471770882815487190701450638520750441585495244800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree102 tree105
attribute [irreducible] tree101
private theorem accepted_101 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox101) tree101 = true := by
  simp only [tree101,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox101 1 (1406216246585018060802172471770882815487190701450638520750441585495244800000000000000000000000 : Int) false,decode_split denominator ibox101 1 (1406216246585018060802172471770882815487190701450638520750441585495244800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_102 h,accepted_105 h⟩
private noncomputable def tree100 : TapeTree := .split 2 (((865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree101 tree110
attribute [irreducible] tree100
private theorem accepted_100 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox100) tree100 = true := by
  simp only [tree100,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox100 2 (865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) false,decode_split denominator ibox100 2 (865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_101 h,accepted_110 h⟩
private noncomputable def tree99 : TapeTree := .split 1 (((1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree100 tree147
attribute [irreducible] tree99
private theorem accepted_99 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox99) tree99 = true := by
  simp only [tree99,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox99 1 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) false,decode_split denominator ibox99 1 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_100 h,accepted_147 h⟩
private noncomputable def tree98 : TapeTree := .centered (candidateRows ibox98) (candidateRows (FixedTape.midBox ibox98))
attribute [irreducible] tree98
private theorem sign_98 : 2*denominator*(computed denominator (FixedTape.midBox ibox98)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox98).gradient k).lo.natAbs ((computed denominator ibox98).gradient k).hi.natAbs : Int)*((ibox98 k).hi-(ibox98 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox98
    (computed denominator ibox98) (computed denominator (FixedTape.midBox ibox98))
    (by decide +kernel)
private theorem midpoint_even_98 : ∀ k, 2 ∣ (ibox98 k).lo+(ibox98 k).hi := by decide +kernel
private theorem accepted_98 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox98) tree98 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox98 midpoint_even_98
  simp only [tree98,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox98,candidate_valid h (FixedTape.midBox ibox98),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox98 83 (FixedTape.rowsAux denominator ibox98 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox98) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_98
private noncomputable def tree97 : TapeTree := .centered (candidateRows ibox97) (candidateRows (FixedTape.midBox ibox97))
attribute [irreducible] tree97
private theorem sign_97 : 2*denominator*(computed denominator (FixedTape.midBox ibox97)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox97).gradient k).lo.natAbs ((computed denominator ibox97).gradient k).hi.natAbs : Int)*((ibox97 k).hi-(ibox97 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox97
    (computed denominator ibox97) (computed denominator (FixedTape.midBox ibox97))
    (by decide +kernel)
private theorem midpoint_even_97 : ∀ k, 2 ∣ (ibox97 k).lo+(ibox97 k).hi := by decide +kernel
private theorem accepted_97 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox97) tree97 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox97 midpoint_even_97
  simp only [tree97,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox97,candidate_valid h (FixedTape.midBox ibox97),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox97 83 (FixedTape.rowsAux denominator ibox97 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox97) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_97
private noncomputable def tree96 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree97 tree98
attribute [irreducible] tree96
private theorem accepted_96 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox96) tree96 = true := by
  simp only [tree96,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox96 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox96 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_97 h,accepted_98 h⟩
private noncomputable def tree95 : TapeTree := .centered (candidateRows ibox95) (candidateRows (FixedTape.midBox ibox95))
attribute [irreducible] tree95
private theorem sign_95 : 2*denominator*(computed denominator (FixedTape.midBox ibox95)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox95).gradient k).lo.natAbs ((computed denominator ibox95).gradient k).hi.natAbs : Int)*((ibox95 k).hi-(ibox95 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox95
    (computed denominator ibox95) (computed denominator (FixedTape.midBox ibox95))
    (by decide +kernel)
private theorem midpoint_even_95 : ∀ k, 2 ∣ (ibox95 k).lo+(ibox95 k).hi := by decide +kernel
private theorem accepted_95 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox95) tree95 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox95 midpoint_even_95
  simp only [tree95,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox95,candidate_valid h (FixedTape.midBox ibox95),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox95 83 (FixedTape.rowsAux denominator ibox95 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox95) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_95
private noncomputable def tree94 : TapeTree := .split 2 (((1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree95 tree96
attribute [irreducible] tree94
private theorem accepted_94 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox94) tree94 = true := by
  simp only [tree94,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox94 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) false,decode_split denominator ibox94 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_95 h,accepted_96 h⟩
private noncomputable def tree93 : TapeTree := .centered (candidateRows ibox93) (candidateRows (FixedTape.midBox ibox93))
attribute [irreducible] tree93
private theorem sign_93 : 2*denominator*(computed denominator (FixedTape.midBox ibox93)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox93).gradient k).lo.natAbs ((computed denominator ibox93).gradient k).hi.natAbs : Int)*((ibox93 k).hi-(ibox93 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox93
    (computed denominator ibox93) (computed denominator (FixedTape.midBox ibox93))
    (by decide +kernel)
private theorem midpoint_even_93 : ∀ k, 2 ∣ (ibox93 k).lo+(ibox93 k).hi := by decide +kernel
private theorem accepted_93 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox93) tree93 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox93 midpoint_even_93
  simp only [tree93,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox93,candidate_valid h (FixedTape.midBox ibox93),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox93 83 (FixedTape.rowsAux denominator ibox93 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox93) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_93
private noncomputable def tree92 : TapeTree := .centered (candidateRows ibox92) (candidateRows (FixedTape.midBox ibox92))
attribute [irreducible] tree92
private theorem sign_92 : 2*denominator*(computed denominator (FixedTape.midBox ibox92)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox92).gradient k).lo.natAbs ((computed denominator ibox92).gradient k).hi.natAbs : Int)*((ibox92 k).hi-(ibox92 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox92
    (computed denominator ibox92) (computed denominator (FixedTape.midBox ibox92))
    (by decide +kernel)
private theorem midpoint_even_92 : ∀ k, 2 ∣ (ibox92 k).lo+(ibox92 k).hi := by decide +kernel
private theorem accepted_92 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox92) tree92 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox92 midpoint_even_92
  simp only [tree92,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox92,candidate_valid h (FixedTape.midBox ibox92),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox92 83 (FixedTape.rowsAux denominator ibox92 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox92) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_92
private noncomputable def tree91 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree92 tree93
attribute [irreducible] tree91
private theorem accepted_91 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox91) tree91 = true := by
  simp only [tree91,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox91 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox91 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_92 h,accepted_93 h⟩
private noncomputable def tree90 : TapeTree := .centered (candidateRows ibox90) (candidateRows (FixedTape.midBox ibox90))
attribute [irreducible] tree90
private theorem sign_90 : 2*denominator*(computed denominator (FixedTape.midBox ibox90)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox90).gradient k).lo.natAbs ((computed denominator ibox90).gradient k).hi.natAbs : Int)*((ibox90 k).hi-(ibox90 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox90
    (computed denominator ibox90) (computed denominator (FixedTape.midBox ibox90))
    (by decide +kernel)
private theorem midpoint_even_90 : ∀ k, 2 ∣ (ibox90 k).lo+(ibox90 k).hi := by decide +kernel
private theorem accepted_90 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox90) tree90 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox90 midpoint_even_90
  simp only [tree90,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox90,candidate_valid h (FixedTape.midBox ibox90),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox90 83 (FixedTape.rowsAux denominator ibox90 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox90) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_90
private noncomputable def tree89 : TapeTree := .split 2 (((1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree90 tree91
attribute [irreducible] tree89
private theorem accepted_89 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox89) tree89 = true := by
  simp only [tree89,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox89 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) false,decode_split denominator ibox89 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_90 h,accepted_91 h⟩
private noncomputable def tree88 : TapeTree := .split 1 (((1243960525825208284555767955797319413700207158975564845279236787168870400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree89 tree94
attribute [irreducible] tree88
private theorem accepted_88 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox88) tree88 = true := by
  simp only [tree88,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox88 1 (1243960525825208284555767955797319413700207158975564845279236787168870400000000000000000000000 : Int) false,decode_split denominator ibox88 1 (1243960525825208284555767955797319413700207158975564845279236787168870400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_89 h,accepted_94 h⟩
private noncomputable def tree87 : TapeTree := .centered (candidateRows ibox87) (candidateRows (FixedTape.midBox ibox87))
attribute [irreducible] tree87
private theorem sign_87 : 2*denominator*(computed denominator (FixedTape.midBox ibox87)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox87).gradient k).lo.natAbs ((computed denominator ibox87).gradient k).hi.natAbs : Int)*((ibox87 k).hi-(ibox87 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox87
    (computed denominator ibox87) (computed denominator (FixedTape.midBox ibox87))
    (by decide +kernel)
private theorem midpoint_even_87 : ∀ k, 2 ∣ (ibox87 k).lo+(ibox87 k).hi := by decide +kernel
private theorem accepted_87 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox87) tree87 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox87 midpoint_even_87
  simp only [tree87,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox87,candidate_valid h (FixedTape.midBox ibox87),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox87 83 (FixedTape.rowsAux denominator ibox87 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox87) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_87
private noncomputable def tree86 : TapeTree := .centered (candidateRows ibox86) (candidateRows (FixedTape.midBox ibox86))
attribute [irreducible] tree86
private theorem sign_86 : 2*denominator*(computed denominator (FixedTape.midBox ibox86)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox86).gradient k).lo.natAbs ((computed denominator ibox86).gradient k).hi.natAbs : Int)*((ibox86 k).hi-(ibox86 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox86
    (computed denominator ibox86) (computed denominator (FixedTape.midBox ibox86))
    (by decide +kernel)
private theorem midpoint_even_86 : ∀ k, 2 ∣ (ibox86 k).lo+(ibox86 k).hi := by decide +kernel
private theorem accepted_86 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox86) tree86 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox86 midpoint_even_86
  simp only [tree86,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox86,candidate_valid h (FixedTape.midBox ibox86),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox86 83 (FixedTape.rowsAux denominator ibox86 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox86) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_86
private noncomputable def tree85 : TapeTree := .split 1 (((1243960525825208284555767955797319413700207158975564845279236787168870400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree86 tree87
attribute [irreducible] tree85
private theorem accepted_85 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox85) tree85 = true := by
  simp only [tree85,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox85 1 (1243960525825208284555767955797319413700207158975564845279236787168870400000000000000000000000 : Int) false,decode_split denominator ibox85 1 (1243960525825208284555767955797319413700207158975564845279236787168870400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_86 h,accepted_87 h⟩
private noncomputable def tree84 : TapeTree := .split 2 (((1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree85 tree88
attribute [irreducible] tree84
private theorem accepted_84 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox84) tree84 = true := by
  simp only [tree84,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox84 2 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) false,decode_split denominator ibox84 2 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_85 h,accepted_88 h⟩
private noncomputable def tree83 : TapeTree := .centered (candidateRows ibox83) (candidateRows (FixedTape.midBox ibox83))
attribute [irreducible] tree83
private theorem sign_83 : 2*denominator*(computed denominator (FixedTape.midBox ibox83)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox83).gradient k).lo.natAbs ((computed denominator ibox83).gradient k).hi.natAbs : Int)*((ibox83 k).hi-(ibox83 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox83
    (computed denominator ibox83) (computed denominator (FixedTape.midBox ibox83))
    (by decide +kernel)
private theorem midpoint_even_83 : ∀ k, 2 ∣ (ibox83 k).lo+(ibox83 k).hi := by decide +kernel
private theorem accepted_83 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox83) tree83 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox83 midpoint_even_83
  simp only [tree83,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox83,candidate_valid h (FixedTape.midBox ibox83),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox83 83 (FixedTape.rowsAux denominator ibox83 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox83) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_83
private noncomputable def tree82 : TapeTree := .centered (candidateRows ibox82) (candidateRows (FixedTape.midBox ibox82))
attribute [irreducible] tree82
private theorem sign_82 : 2*denominator*(computed denominator (FixedTape.midBox ibox82)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox82).gradient k).lo.natAbs ((computed denominator ibox82).gradient k).hi.natAbs : Int)*((ibox82 k).hi-(ibox82 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox82
    (computed denominator ibox82) (computed denominator (FixedTape.midBox ibox82))
    (by decide +kernel)
private theorem midpoint_even_82 : ∀ k, 2 ∣ (ibox82 k).lo+(ibox82 k).hi := by decide +kernel
private theorem accepted_82 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox82) tree82 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox82 midpoint_even_82
  simp only [tree82,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox82,candidate_valid h (FixedTape.midBox ibox82),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox82 83 (FixedTape.rowsAux denominator ibox82 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox82) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_82
private noncomputable def tree81 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree82 tree83
attribute [irreducible] tree81
private theorem accepted_81 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox81) tree81 = true := by
  simp only [tree81,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox81 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox81 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_82 h,accepted_83 h⟩
private noncomputable def tree80 : TapeTree := .centered (candidateRows ibox80) (candidateRows (FixedTape.midBox ibox80))
attribute [irreducible] tree80
private theorem sign_80 : 2*denominator*(computed denominator (FixedTape.midBox ibox80)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox80).gradient k).lo.natAbs ((computed denominator ibox80).gradient k).hi.natAbs : Int)*((ibox80 k).hi-(ibox80 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox80
    (computed denominator ibox80) (computed denominator (FixedTape.midBox ibox80))
    (by decide +kernel)
private theorem midpoint_even_80 : ∀ k, 2 ∣ (ibox80 k).lo+(ibox80 k).hi := by decide +kernel
private theorem accepted_80 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox80) tree80 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox80 midpoint_even_80
  simp only [tree80,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox80,candidate_valid h (FixedTape.midBox ibox80),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox80 83 (FixedTape.rowsAux denominator ibox80 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox80) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_80
private noncomputable def tree79 : TapeTree := .split 2 (((1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree80 tree81
attribute [irreducible] tree79
private theorem accepted_79 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox79) tree79 = true := by
  simp only [tree79,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox79 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) false,decode_split denominator ibox79 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_80 h,accepted_81 h⟩
private noncomputable def tree78 : TapeTree := .centered (candidateRows ibox78) (candidateRows (FixedTape.midBox ibox78))
attribute [irreducible] tree78
private theorem sign_78 : 2*denominator*(computed denominator (FixedTape.midBox ibox78)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox78).gradient k).lo.natAbs ((computed denominator ibox78).gradient k).hi.natAbs : Int)*((ibox78 k).hi-(ibox78 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox78
    (computed denominator ibox78) (computed denominator (FixedTape.midBox ibox78))
    (by decide +kernel)
private theorem midpoint_even_78 : ∀ k, 2 ∣ (ibox78 k).lo+(ibox78 k).hi := by decide +kernel
private theorem accepted_78 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox78) tree78 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox78 midpoint_even_78
  simp only [tree78,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox78,candidate_valid h (FixedTape.midBox ibox78),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox78 83 (FixedTape.rowsAux denominator ibox78 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox78) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_78
private noncomputable def tree77 : TapeTree := .centered (candidateRows ibox77) (candidateRows (FixedTape.midBox ibox77))
attribute [irreducible] tree77
private theorem sign_77 : 2*denominator*(computed denominator (FixedTape.midBox ibox77)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox77).gradient k).lo.natAbs ((computed denominator ibox77).gradient k).hi.natAbs : Int)*((ibox77 k).hi-(ibox77 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox77
    (computed denominator ibox77) (computed denominator (FixedTape.midBox ibox77))
    (by decide +kernel)
private theorem midpoint_even_77 : ∀ k, 2 ∣ (ibox77 k).lo+(ibox77 k).hi := by decide +kernel
private theorem accepted_77 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox77) tree77 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox77 midpoint_even_77
  simp only [tree77,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox77,candidate_valid h (FixedTape.midBox ibox77),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox77 83 (FixedTape.rowsAux denominator ibox77 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox77) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_77
private noncomputable def tree76 : TapeTree := .split 2 (((1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree77 tree78
attribute [irreducible] tree76
private theorem accepted_76 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox76) tree76 = true := by
  simp only [tree76,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox76 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) false,decode_split denominator ibox76 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_77 h,accepted_78 h⟩
private noncomputable def tree75 : TapeTree := .split 1 (((1135790045318668433724831611814943812508884797325515728298433588284620800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree76 tree79
attribute [irreducible] tree75
private theorem accepted_75 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox75) tree75 = true := by
  simp only [tree75,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox75 1 (1135790045318668433724831611814943812508884797325515728298433588284620800000000000000000000000 : Int) false,decode_split denominator ibox75 1 (1135790045318668433724831611814943812508884797325515728298433588284620800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_76 h,accepted_79 h⟩
private noncomputable def tree74 : TapeTree := .centered (candidateRows ibox74) (candidateRows (FixedTape.midBox ibox74))
attribute [irreducible] tree74
private theorem sign_74 : 2*denominator*(computed denominator (FixedTape.midBox ibox74)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox74).gradient k).lo.natAbs ((computed denominator ibox74).gradient k).hi.natAbs : Int)*((ibox74 k).hi-(ibox74 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox74
    (computed denominator ibox74) (computed denominator (FixedTape.midBox ibox74))
    (by decide +kernel)
private theorem midpoint_even_74 : ∀ k, 2 ∣ (ibox74 k).lo+(ibox74 k).hi := by decide +kernel
private theorem accepted_74 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox74) tree74 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox74 midpoint_even_74
  simp only [tree74,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox74,candidate_valid h (FixedTape.midBox ibox74),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox74 83 (FixedTape.rowsAux denominator ibox74 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox74) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_74
private noncomputable def tree73 : TapeTree := .centered (candidateRows ibox73) (candidateRows (FixedTape.midBox ibox73))
attribute [irreducible] tree73
private theorem sign_73 : 2*denominator*(computed denominator (FixedTape.midBox ibox73)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox73).gradient k).lo.natAbs ((computed denominator ibox73).gradient k).hi.natAbs : Int)*((ibox73 k).hi-(ibox73 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox73
    (computed denominator ibox73) (computed denominator (FixedTape.midBox ibox73))
    (by decide +kernel)
private theorem midpoint_even_73 : ∀ k, 2 ∣ (ibox73 k).lo+(ibox73 k).hi := by decide +kernel
private theorem accepted_73 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox73) tree73 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox73 midpoint_even_73
  simp only [tree73,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox73,candidate_valid h (FixedTape.midBox ibox73),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox73 83 (FixedTape.rowsAux denominator ibox73 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox73) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_73
private noncomputable def tree72 : TapeTree := .split 1 (((1135790045318668433724831611814943812508884797325515728298433588284620800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree73 tree74
attribute [irreducible] tree72
private theorem accepted_72 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox72) tree72 = true := by
  simp only [tree72,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox72 1 (1135790045318668433724831611814943812508884797325515728298433588284620800000000000000000000000 : Int) false,decode_split denominator ibox72 1 (1135790045318668433724831611814943812508884797325515728298433588284620800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_73 h,accepted_74 h⟩
private noncomputable def tree71 : TapeTree := .split 2 (((1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree72 tree75
attribute [irreducible] tree71
private theorem accepted_71 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox71) tree71 = true := by
  simp only [tree71,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox71 2 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) false,decode_split denominator ibox71 2 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_72 h,accepted_75 h⟩
private noncomputable def tree70 : TapeTree := .split 1 (((1189875285571938359140299783806131613104545978150540286788835187726745600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree71 tree84
attribute [irreducible] tree70
private theorem accepted_70 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox70) tree70 = true := by
  simp only [tree70,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox70 1 (1189875285571938359140299783806131613104545978150540286788835187726745600000000000000000000000 : Int) false,decode_split denominator ibox70 1 (1189875285571938359140299783806131613104545978150540286788835187726745600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_71 h,accepted_84 h⟩
private noncomputable def tree69 : TapeTree := .centered (candidateRows ibox69) (candidateRows (FixedTape.midBox ibox69))
attribute [irreducible] tree69
private theorem sign_69 : 2*denominator*(computed denominator (FixedTape.midBox ibox69)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox69).gradient k).lo.natAbs ((computed denominator ibox69).gradient k).hi.natAbs : Int)*((ibox69 k).hi-(ibox69 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox69
    (computed denominator ibox69) (computed denominator (FixedTape.midBox ibox69))
    (by decide +kernel)
private theorem midpoint_even_69 : ∀ k, 2 ∣ (ibox69 k).lo+(ibox69 k).hi := by decide +kernel
private theorem accepted_69 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox69) tree69 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox69 midpoint_even_69
  simp only [tree69,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox69,candidate_valid h (FixedTape.midBox ibox69),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox69 83 (FixedTape.rowsAux denominator ibox69 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox69) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_69
private noncomputable def tree68 : TapeTree := .centered (candidateRows ibox68) (candidateRows (FixedTape.midBox ibox68))
attribute [irreducible] tree68
private theorem sign_68 : 2*denominator*(computed denominator (FixedTape.midBox ibox68)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox68).gradient k).lo.natAbs ((computed denominator ibox68).gradient k).hi.natAbs : Int)*((ibox68 k).hi-(ibox68 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox68
    (computed denominator ibox68) (computed denominator (FixedTape.midBox ibox68))
    (by decide +kernel)
private theorem midpoint_even_68 : ∀ k, 2 ∣ (ibox68 k).lo+(ibox68 k).hi := by decide +kernel
private theorem accepted_68 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox68) tree68 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox68 midpoint_even_68
  simp only [tree68,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox68,candidate_valid h (FixedTape.midBox ibox68),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox68 83 (FixedTape.rowsAux denominator ibox68 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox68) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_68
private noncomputable def tree67 : TapeTree := .split 1 (((1243960525825208284555767955797319413700207158975564845279236787168870400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree68 tree69
attribute [irreducible] tree67
private theorem accepted_67 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox67) tree67 = true := by
  simp only [tree67,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox67 1 (1243960525825208284555767955797319413700207158975564845279236787168870400000000000000000000000 : Int) false,decode_split denominator ibox67 1 (1243960525825208284555767955797319413700207158975564845279236787168870400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_68 h,accepted_69 h⟩
private noncomputable def tree66 : TapeTree := .centered (candidateRows ibox66) (candidateRows (FixedTape.midBox ibox66))
attribute [irreducible] tree66
private theorem sign_66 : 2*denominator*(computed denominator (FixedTape.midBox ibox66)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox66).gradient k).lo.natAbs ((computed denominator ibox66).gradient k).hi.natAbs : Int)*((ibox66 k).hi-(ibox66 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox66
    (computed denominator ibox66) (computed denominator (FixedTape.midBox ibox66))
    (by decide +kernel)
private theorem midpoint_even_66 : ∀ k, 2 ∣ (ibox66 k).lo+(ibox66 k).hi := by decide +kernel
private theorem accepted_66 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox66) tree66 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox66 midpoint_even_66
  simp only [tree66,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox66,candidate_valid h (FixedTape.midBox ibox66),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox66 83 (FixedTape.rowsAux denominator ibox66 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox66) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_66
private noncomputable def tree65 : TapeTree := .centered (candidateRows ibox65) (candidateRows (FixedTape.midBox ibox65))
attribute [irreducible] tree65
private theorem sign_65 : 2*denominator*(computed denominator (FixedTape.midBox ibox65)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox65).gradient k).lo.natAbs ((computed denominator ibox65).gradient k).hi.natAbs : Int)*((ibox65 k).hi-(ibox65 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox65
    (computed denominator ibox65) (computed denominator (FixedTape.midBox ibox65))
    (by decide +kernel)
private theorem midpoint_even_65 : ∀ k, 2 ∣ (ibox65 k).lo+(ibox65 k).hi := by decide +kernel
private theorem accepted_65 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox65) tree65 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox65 midpoint_even_65
  simp only [tree65,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox65,candidate_valid h (FixedTape.midBox ibox65),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox65 83 (FixedTape.rowsAux denominator ibox65 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox65) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_65
private noncomputable def tree64 : TapeTree := .split 1 (((1135790045318668433724831611814943812508884797325515728298433588284620800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree65 tree66
attribute [irreducible] tree64
private theorem accepted_64 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox64) tree64 = true := by
  simp only [tree64,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox64 1 (1135790045318668433724831611814943812508884797325515728298433588284620800000000000000000000000 : Int) false,decode_split denominator ibox64 1 (1135790045318668433724831611814943812508884797325515728298433588284620800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_65 h,accepted_66 h⟩
private noncomputable def tree63 : TapeTree := .split 1 (((1189875285571938359140299783806131613104545978150540286788835187726745600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree64 tree67
attribute [irreducible] tree63
private theorem accepted_63 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox63) tree63 = true := by
  simp only [tree63,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox63 1 (1189875285571938359140299783806131613104545978150540286788835187726745600000000000000000000000 : Int) false,decode_split denominator ibox63 1 (1189875285571938359140299783806131613104545978150540286788835187726745600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_64 h,accepted_67 h⟩
private noncomputable def tree62 : TapeTree := .split 2 (((865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree63 tree70
attribute [irreducible] tree62
private theorem accepted_62 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox62) tree62 = true := by
  simp only [tree62,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox62 2 (865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) false,decode_split denominator ibox62 2 (865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_63 h,accepted_70 h⟩
private noncomputable def tree61 : TapeTree := .centered (candidateRows ibox61) (candidateRows (FixedTape.midBox ibox61))
attribute [irreducible] tree61
private theorem sign_61 : 2*denominator*(computed denominator (FixedTape.midBox ibox61)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox61).gradient k).lo.natAbs ((computed denominator ibox61).gradient k).hi.natAbs : Int)*((ibox61 k).hi-(ibox61 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox61
    (computed denominator ibox61) (computed denominator (FixedTape.midBox ibox61))
    (by decide +kernel)
private theorem midpoint_even_61 : ∀ k, 2 ∣ (ibox61 k).lo+(ibox61 k).hi := by decide +kernel
private theorem accepted_61 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox61) tree61 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox61 midpoint_even_61
  simp only [tree61,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox61,candidate_valid h (FixedTape.midBox ibox61),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox61 83 (FixedTape.rowsAux denominator ibox61 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox61) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_61
private noncomputable def tree60 : TapeTree := .centered (candidateRows ibox60) (candidateRows (FixedTape.midBox ibox60))
attribute [irreducible] tree60
private theorem sign_60 : 2*denominator*(computed denominator (FixedTape.midBox ibox60)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox60).gradient k).lo.natAbs ((computed denominator ibox60).gradient k).hi.natAbs : Int)*((ibox60 k).hi-(ibox60 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox60
    (computed denominator ibox60) (computed denominator (FixedTape.midBox ibox60))
    (by decide +kernel)
private theorem midpoint_even_60 : ∀ k, 2 ∣ (ibox60 k).lo+(ibox60 k).hi := by decide +kernel
private theorem accepted_60 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox60) tree60 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox60 midpoint_even_60
  simp only [tree60,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox60,candidate_valid h (FixedTape.midBox ibox60),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox60 83 (FixedTape.rowsAux denominator ibox60 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox60) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_60
private noncomputable def tree59 : TapeTree := .split 2 (((1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree60 tree61
attribute [irreducible] tree59
private theorem accepted_59 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox59) tree59 = true := by
  simp only [tree59,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox59 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) false,decode_split denominator ibox59 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_60 h,accepted_61 h⟩
private noncomputable def tree58 : TapeTree := .centered (candidateRows ibox58) (candidateRows (FixedTape.midBox ibox58))
attribute [irreducible] tree58
private theorem sign_58 : 2*denominator*(computed denominator (FixedTape.midBox ibox58)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox58).gradient k).lo.natAbs ((computed denominator ibox58).gradient k).hi.natAbs : Int)*((ibox58 k).hi-(ibox58 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox58
    (computed denominator ibox58) (computed denominator (FixedTape.midBox ibox58))
    (by decide +kernel)
private theorem midpoint_even_58 : ∀ k, 2 ∣ (ibox58 k).lo+(ibox58 k).hi := by decide +kernel
private theorem accepted_58 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox58) tree58 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox58 midpoint_even_58
  simp only [tree58,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox58,candidate_valid h (FixedTape.midBox ibox58),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox58 83 (FixedTape.rowsAux denominator ibox58 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox58) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_58
private noncomputable def tree57 : TapeTree := .centered (candidateRows ibox57) (candidateRows (FixedTape.midBox ibox57))
attribute [irreducible] tree57
private theorem sign_57 : 2*denominator*(computed denominator (FixedTape.midBox ibox57)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox57).gradient k).lo.natAbs ((computed denominator ibox57).gradient k).hi.natAbs : Int)*((ibox57 k).hi-(ibox57 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox57
    (computed denominator ibox57) (computed denominator (FixedTape.midBox ibox57))
    (by decide +kernel)
private theorem midpoint_even_57 : ∀ k, 2 ∣ (ibox57 k).lo+(ibox57 k).hi := by decide +kernel
private theorem accepted_57 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox57) tree57 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox57 midpoint_even_57
  simp only [tree57,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox57,candidate_valid h (FixedTape.midBox ibox57),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox57 83 (FixedTape.rowsAux denominator ibox57 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox57) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_57
private noncomputable def tree56 : TapeTree := .split 2 (((1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree57 tree58
attribute [irreducible] tree56
private theorem accepted_56 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox56) tree56 = true := by
  simp only [tree56,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox56 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) false,decode_split denominator ibox56 2 (1514386727091557911633108815753258416678513063100687637731244784379494400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_57 h,accepted_58 h⟩
private noncomputable def tree55 : TapeTree := .split 1 (((1027619564812128582893895267832568211317562435675466611317630389400371200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree56 tree59
attribute [irreducible] tree55
private theorem accepted_55 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox55) tree55 = true := by
  simp only [tree55,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox55 1 (1027619564812128582893895267832568211317562435675466611317630389400371200000000000000000000000 : Int) false,decode_split denominator ibox55 1 (1027619564812128582893895267832568211317562435675466611317630389400371200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_56 h,accepted_59 h⟩
private noncomputable def tree54 : TapeTree := .centered (candidateRows ibox54) (candidateRows (FixedTape.midBox ibox54))
attribute [irreducible] tree54
private theorem sign_54 : 2*denominator*(computed denominator (FixedTape.midBox ibox54)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox54).gradient k).lo.natAbs ((computed denominator ibox54).gradient k).hi.natAbs : Int)*((ibox54 k).hi-(ibox54 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox54
    (computed denominator ibox54) (computed denominator (FixedTape.midBox ibox54))
    (by decide +kernel)
private theorem midpoint_even_54 : ∀ k, 2 ∣ (ibox54 k).lo+(ibox54 k).hi := by decide +kernel
private theorem accepted_54 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox54) tree54 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox54 midpoint_even_54
  simp only [tree54,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox54,candidate_valid h (FixedTape.midBox ibox54),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox54 83 (FixedTape.rowsAux denominator ibox54 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox54) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_54
private noncomputable def tree53 : TapeTree := .centered (candidateRows ibox53) (candidateRows (FixedTape.midBox ibox53))
attribute [irreducible] tree53
private theorem sign_53 : 2*denominator*(computed denominator (FixedTape.midBox ibox53)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox53).gradient k).lo.natAbs ((computed denominator ibox53).gradient k).hi.natAbs : Int)*((ibox53 k).hi-(ibox53 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox53
    (computed denominator ibox53) (computed denominator (FixedTape.midBox ibox53))
    (by decide +kernel)
private theorem midpoint_even_53 : ∀ k, 2 ∣ (ibox53 k).lo+(ibox53 k).hi := by decide +kernel
private theorem accepted_53 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox53) tree53 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox53 midpoint_even_53
  simp only [tree53,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox53,candidate_valid h (FixedTape.midBox ibox53),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox53 83 (FixedTape.rowsAux denominator ibox53 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox53) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_53
private noncomputable def tree52 : TapeTree := .split 1 (((1027619564812128582893895267832568211317562435675466611317630389400371200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree53 tree54
attribute [irreducible] tree52
private theorem accepted_52 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox52) tree52 = true := by
  simp only [tree52,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox52 1 (1027619564812128582893895267832568211317562435675466611317630389400371200000000000000000000000 : Int) false,decode_split denominator ibox52 1 (1027619564812128582893895267832568211317562435675466611317630389400371200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_53 h,accepted_54 h⟩
private noncomputable def tree51 : TapeTree := .split 2 (((1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree52 tree55
attribute [irreducible] tree51
private theorem accepted_51 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox51) tree51 = true := by
  simp only [tree51,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox51 2 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) false,decode_split denominator ibox51 2 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_52 h,accepted_55 h⟩
private noncomputable def tree50 : TapeTree := .centered (candidateRows ibox50) (candidateRows (FixedTape.midBox ibox50))
attribute [irreducible] tree50
private theorem sign_50 : 2*denominator*(computed denominator (FixedTape.midBox ibox50)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox50).gradient k).lo.natAbs ((computed denominator ibox50).gradient k).hi.natAbs : Int)*((ibox50 k).hi-(ibox50 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox50
    (computed denominator ibox50) (computed denominator (FixedTape.midBox ibox50))
    (by decide +kernel)
private theorem midpoint_even_50 : ∀ k, 2 ∣ (ibox50 k).lo+(ibox50 k).hi := by decide +kernel
private theorem accepted_50 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox50) tree50 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox50 midpoint_even_50
  simp only [tree50,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox50,candidate_valid h (FixedTape.midBox ibox50),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox50 83 (FixedTape.rowsAux denominator ibox50 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox50) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_50
private noncomputable def tree49 : TapeTree := .face 0 true (candidateRows ibox49) tree50
attribute [irreducible] tree49
private theorem sign_49 : 0 ≤ ((computed denominator ibox49).gradient 0).lo := by decide +kernel
private theorem accepted_49 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox49) tree49 = true := by
  simp only [tree49,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox49,?_,accepted_50 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox49)).gradient 0).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox49).gradient 0).lo) denominator_positive).2 sign_49
private noncomputable def tree48 : TapeTree := .centered (candidateRows ibox48) (candidateRows (FixedTape.midBox ibox48))
attribute [irreducible] tree48
private theorem sign_48 : 2*denominator*(computed denominator (FixedTape.midBox ibox48)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox48).gradient k).lo.natAbs ((computed denominator ibox48).gradient k).hi.natAbs : Int)*((ibox48 k).hi-(ibox48 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox48
    (computed denominator ibox48) (computed denominator (FixedTape.midBox ibox48))
    (by decide +kernel)
private theorem midpoint_even_48 : ∀ k, 2 ∣ (ibox48 k).lo+(ibox48 k).hi := by decide +kernel
private theorem accepted_48 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox48) tree48 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox48 midpoint_even_48
  simp only [tree48,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox48,candidate_valid h (FixedTape.midBox ibox48),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox48 83 (FixedTape.rowsAux denominator ibox48 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox48) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_48
private noncomputable def tree47 : TapeTree := .split 1 (((919449084305588732062958923850192610126240074025417494336827190516121600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree48 tree49
attribute [irreducible] tree47
private theorem accepted_47 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox47) tree47 = true := by
  simp only [tree47,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox47 1 (919449084305588732062958923850192610126240074025417494336827190516121600000000000000000000000 : Int) false,decode_split denominator ibox47 1 (919449084305588732062958923850192610126240074025417494336827190516121600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_48 h,accepted_49 h⟩
private noncomputable def tree46 : TapeTree := .centered (candidateRows ibox46) (candidateRows (FixedTape.midBox ibox46))
attribute [irreducible] tree46
private theorem sign_46 : 2*denominator*(computed denominator (FixedTape.midBox ibox46)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox46).gradient k).lo.natAbs ((computed denominator ibox46).gradient k).hi.natAbs : Int)*((ibox46 k).hi-(ibox46 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox46
    (computed denominator ibox46) (computed denominator (FixedTape.midBox ibox46))
    (by decide +kernel)
private theorem midpoint_even_46 : ∀ k, 2 ∣ (ibox46 k).lo+(ibox46 k).hi := by decide +kernel
private theorem accepted_46 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox46) tree46 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox46 midpoint_even_46
  simp only [tree46,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox46,candidate_valid h (FixedTape.midBox ibox46),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox46 83 (FixedTape.rowsAux denominator ibox46 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox46) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_46
private noncomputable def tree45 : TapeTree := .split 2 (((1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree46 tree47
attribute [irreducible] tree45
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox45 2 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) false,decode_split denominator ibox45 2 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_46 h,accepted_47 h⟩
private noncomputable def tree44 : TapeTree := .split 1 (((973534324558858657478427095841380410721901254850442052827228789958246400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree45 tree51
attribute [irreducible] tree44
private theorem accepted_44 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox44) tree44 = true := by
  simp only [tree44,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox44 1 (973534324558858657478427095841380410721901254850442052827228789958246400000000000000000000000 : Int) false,decode_split denominator ibox44 1 (973534324558858657478427095841380410721901254850442052827228789958246400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_45 h,accepted_51 h⟩
private noncomputable def tree43 : TapeTree := .centered (candidateRows ibox43) (candidateRows (FixedTape.midBox ibox43))
attribute [irreducible] tree43
private theorem sign_43 : 2*denominator*(computed denominator (FixedTape.midBox ibox43)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox43).gradient k).lo.natAbs ((computed denominator ibox43).gradient k).hi.natAbs : Int)*((ibox43 k).hi-(ibox43 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox43
    (computed denominator ibox43) (computed denominator (FixedTape.midBox ibox43))
    (by decide +kernel)
private theorem midpoint_even_43 : ∀ k, 2 ∣ (ibox43 k).lo+(ibox43 k).hi := by decide +kernel
private theorem accepted_43 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox43) tree43 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox43 midpoint_even_43
  simp only [tree43,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox43,candidate_valid h (FixedTape.midBox ibox43),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox43 83 (FixedTape.rowsAux denominator ibox43 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox43) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_43
private noncomputable def tree42 : TapeTree := .centered (candidateRows ibox42) (candidateRows (FixedTape.midBox ibox42))
attribute [irreducible] tree42
private theorem sign_42 : 2*denominator*(computed denominator (FixedTape.midBox ibox42)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox42).gradient k).lo.natAbs ((computed denominator ibox42).gradient k).hi.natAbs : Int)*((ibox42 k).hi-(ibox42 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox42
    (computed denominator ibox42) (computed denominator (FixedTape.midBox ibox42))
    (by decide +kernel)
private theorem midpoint_even_42 : ∀ k, 2 ∣ (ibox42 k).lo+(ibox42 k).hi := by decide +kernel
private theorem accepted_42 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox42) tree42 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox42 midpoint_even_42
  simp only [tree42,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox42,candidate_valid h (FixedTape.midBox ibox42),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox42 83 (FixedTape.rowsAux denominator ibox42 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox42) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_42
private noncomputable def tree41 : TapeTree := .split 1 (((1027619564812128582893895267832568211317562435675466611317630389400371200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree42 tree43
attribute [irreducible] tree41
private theorem accepted_41 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox41) tree41 = true := by
  simp only [tree41,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox41 1 (1027619564812128582893895267832568211317562435675466611317630389400371200000000000000000000000 : Int) false,decode_split denominator ibox41 1 (1027619564812128582893895267832568211317562435675466611317630389400371200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_42 h,accepted_43 h⟩
private noncomputable def tree40 : TapeTree := .centered (candidateRows ibox40) (candidateRows (FixedTape.midBox ibox40))
attribute [irreducible] tree40
private theorem sign_40 : 2*denominator*(computed denominator (FixedTape.midBox ibox40)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox40).gradient k).lo.natAbs ((computed denominator ibox40).gradient k).hi.natAbs : Int)*((ibox40 k).hi-(ibox40 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox40
    (computed denominator ibox40) (computed denominator (FixedTape.midBox ibox40))
    (by decide +kernel)
private theorem midpoint_even_40 : ∀ k, 2 ∣ (ibox40 k).lo+(ibox40 k).hi := by decide +kernel
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox40 midpoint_even_40
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox40,candidate_valid h (FixedTape.midBox ibox40),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox40 83 (FixedTape.rowsAux denominator ibox40 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox40) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_40
private noncomputable def tree39 : TapeTree := .split 1 (((973534324558858657478427095841380410721901254850442052827228789958246400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree40 tree41
attribute [irreducible] tree39
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox39 1 (973534324558858657478427095841380410721901254850442052827228789958246400000000000000000000000 : Int) false,decode_split denominator ibox39 1 (973534324558858657478427095841380410721901254850442052827228789958246400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_40 h,accepted_41 h⟩
private noncomputable def tree38 : TapeTree := .split 2 (((865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree39 tree44
attribute [irreducible] tree38
private theorem accepted_38 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox38) tree38 = true := by
  simp only [tree38,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox38 2 (865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) false,decode_split denominator ibox38 2 (865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_39 h,accepted_44 h⟩
private noncomputable def tree37 : TapeTree := .split 1 (((1081704805065398508309363439823756011913223616500491169808031988842496000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree38 tree62
attribute [irreducible] tree37
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox37 1 (1081704805065398508309363439823756011913223616500491169808031988842496000000000000000000000000 : Int) false,decode_split denominator ibox37 1 (1081704805065398508309363439823756011913223616500491169808031988842496000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_38 h,accepted_62 h⟩
private noncomputable def tree36 : TapeTree := .split 1 (((1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree37 tree99
attribute [irreducible] tree36
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox36 1 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) false,decode_split denominator ibox36 1 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_37 h,accepted_99 h⟩
private noncomputable def tree35 : TapeTree := .centered (candidateRows ibox35) (candidateRows (FixedTape.midBox ibox35))
attribute [irreducible] tree35
private theorem sign_35 : 2*denominator*(computed denominator (FixedTape.midBox ibox35)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox35).gradient k).lo.natAbs ((computed denominator ibox35).gradient k).hi.natAbs : Int)*((ibox35 k).hi-(ibox35 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox35
    (computed denominator ibox35) (computed denominator (FixedTape.midBox ibox35))
    (by decide +kernel)
private theorem midpoint_even_35 : ∀ k, 2 ∣ (ibox35 k).lo+(ibox35 k).hi := by decide +kernel
private theorem accepted_35 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox35) tree35 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox35 midpoint_even_35
  simp only [tree35,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox35,candidate_valid h (FixedTape.midBox ibox35),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox35 83 (FixedTape.rowsAux denominator ibox35 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox35) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_35
private noncomputable def tree34 : TapeTree := .centered (candidateRows ibox34) (candidateRows (FixedTape.midBox ibox34))
attribute [irreducible] tree34
private theorem sign_34 : 2*denominator*(computed denominator (FixedTape.midBox ibox34)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox34).gradient k).lo.natAbs ((computed denominator ibox34).gradient k).hi.natAbs : Int)*((ibox34 k).hi-(ibox34 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox34
    (computed denominator ibox34) (computed denominator (FixedTape.midBox ibox34))
    (by decide +kernel)
private theorem midpoint_even_34 : ∀ k, 2 ∣ (ibox34 k).lo+(ibox34 k).hi := by decide +kernel
private theorem accepted_34 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox34) tree34 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox34 midpoint_even_34
  simp only [tree34,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox34,candidate_valid h (FixedTape.midBox ibox34),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox34 83 (FixedTape.rowsAux denominator ibox34 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox34) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_34
private noncomputable def tree33 : TapeTree := .split 1 (((811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree34 tree35
attribute [irreducible] tree33
private theorem accepted_33 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox33) tree33 = true := by
  simp only [tree33,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox33 1 (811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 : Int) false,decode_split denominator ibox33 1 (811278603799048881232022579867817008934917712375368377356023991631872000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_34 h,accepted_35 h⟩
private noncomputable def tree32 : TapeTree := .centered (candidateRows ibox32) (candidateRows (FixedTape.midBox ibox32))
attribute [irreducible] tree32
private theorem sign_32 : 2*denominator*(computed denominator (FixedTape.midBox ibox32)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox32).gradient k).lo.natAbs ((computed denominator ibox32).gradient k).hi.natAbs : Int)*((ibox32 k).hi-(ibox32 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox32
    (computed denominator ibox32) (computed denominator (FixedTape.midBox ibox32))
    (by decide +kernel)
private theorem midpoint_even_32 : ∀ k, 2 ∣ (ibox32 k).lo+(ibox32 k).hi := by decide +kernel
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox32 midpoint_even_32
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox32,candidate_valid h (FixedTape.midBox ibox32),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox32 83 (FixedTape.rowsAux denominator ibox32 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox32) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_32
private noncomputable def tree31 : TapeTree := .split 2 (((1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree32 tree33
attribute [irreducible] tree31
private theorem accepted_31 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox31) tree31 = true := by
  simp only [tree31,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox31 2 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) false,decode_split denominator ibox31 2 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_32 h,accepted_33 h⟩
private noncomputable def tree30 : TapeTree := .centered (candidateRows ibox30) (candidateRows (FixedTape.midBox ibox30))
attribute [irreducible] tree30
private theorem sign_30 : 2*denominator*(computed denominator (FixedTape.midBox ibox30)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox30).gradient k).lo.natAbs ((computed denominator ibox30).gradient k).hi.natAbs : Int)*((ibox30 k).hi-(ibox30 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox30
    (computed denominator ibox30) (computed denominator (FixedTape.midBox ibox30))
    (by decide +kernel)
private theorem midpoint_even_30 : ∀ k, 2 ∣ (ibox30 k).lo+(ibox30 k).hi := by decide +kernel
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox30 midpoint_even_30
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox30,candidate_valid h (FixedTape.midBox ibox30),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox30 83 (FixedTape.rowsAux denominator ibox30 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox30) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_30
private noncomputable def tree29 : TapeTree := .centered (candidateRows ibox29) (candidateRows (FixedTape.midBox ibox29))
attribute [irreducible] tree29
private theorem sign_29 : 2*denominator*(computed denominator (FixedTape.midBox ibox29)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox29).gradient k).lo.natAbs ((computed denominator ibox29).gradient k).hi.natAbs : Int)*((ibox29 k).hi-(ibox29 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox29
    (computed denominator ibox29) (computed denominator (FixedTape.midBox ibox29))
    (by decide +kernel)
private theorem midpoint_even_29 : ∀ k, 2 ∣ (ibox29 k).lo+(ibox29 k).hi := by decide +kernel
private theorem accepted_29 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox29) tree29 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox29 midpoint_even_29
  simp only [tree29,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox29,candidate_valid h (FixedTape.midBox ibox29),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox29 83 (FixedTape.rowsAux denominator ibox29 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox29) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_29
private noncomputable def tree28 : TapeTree := .split 0 (((1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) : ℚ)/(denominator : ℚ)) tree29 tree30
attribute [irreducible] tree28
private theorem accepted_28 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox28) tree28 = true := by
  simp only [tree28,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox28 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) false,decode_split denominator ibox28 0 (1667628241142489424667858239882877628198936532705244522159308862825043723095039404933120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_29 h,accepted_30 h⟩
private noncomputable def tree27 : TapeTree := .centered (candidateRows ibox27) (candidateRows (FixedTape.midBox ibox27))
attribute [irreducible] tree27
private theorem sign_27 : 2*denominator*(computed denominator (FixedTape.midBox ibox27)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox27).gradient k).lo.natAbs ((computed denominator ibox27).gradient k).hi.natAbs : Int)*((ibox27 k).hi-(ibox27 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox27
    (computed denominator ibox27) (computed denominator (FixedTape.midBox ibox27))
    (by decide +kernel)
private theorem midpoint_even_27 : ∀ k, 2 ∣ (ibox27 k).lo+(ibox27 k).hi := by decide +kernel
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox27 midpoint_even_27
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox27,candidate_valid h (FixedTape.midBox ibox27),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox27 83 (FixedTape.rowsAux denominator ibox27 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox27) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_27
private noncomputable def tree26 : TapeTree := .split 2 (((1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree27 tree28
attribute [irreducible] tree26
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox26 2 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) false,decode_split denominator ibox26 2 (1298045766078478209971236127788507214295868339800589403769638386610995200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_27 h,accepted_28 h⟩
private noncomputable def tree25 : TapeTree := .split 1 (((757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree26 tree31
attribute [irreducible] tree25
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox25 1 (757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 : Int) false,decode_split denominator ibox25 1 (757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_26 h,accepted_31 h⟩
private noncomputable def tree24 : TapeTree := .centered (candidateRows ibox24) (candidateRows (FixedTape.midBox ibox24))
attribute [irreducible] tree24
private theorem sign_24 : 2*denominator*(computed denominator (FixedTape.midBox ibox24)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox24).gradient k).lo.natAbs ((computed denominator ibox24).gradient k).hi.natAbs : Int)*((ibox24 k).hi-(ibox24 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox24
    (computed denominator ibox24) (computed denominator (FixedTape.midBox ibox24))
    (by decide +kernel)
private theorem midpoint_even_24 : ∀ k, 2 ∣ (ibox24 k).lo+(ibox24 k).hi := by decide +kernel
private theorem accepted_24 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox24) tree24 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox24 midpoint_even_24
  simp only [tree24,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox24,candidate_valid h (FixedTape.midBox ibox24),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox24 83 (FixedTape.rowsAux denominator ibox24 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox24) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_24
private noncomputable def tree23 : TapeTree := .centered (candidateRows ibox23) (candidateRows (FixedTape.midBox ibox23))
attribute [irreducible] tree23
private theorem sign_23 : 2*denominator*(computed denominator (FixedTape.midBox ibox23)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox23).gradient k).lo.natAbs ((computed denominator ibox23).gradient k).hi.natAbs : Int)*((ibox23 k).hi-(ibox23 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox23
    (computed denominator ibox23) (computed denominator (FixedTape.midBox ibox23))
    (by decide +kernel)
private theorem midpoint_even_23 : ∀ k, 2 ∣ (ibox23 k).lo+(ibox23 k).hi := by decide +kernel
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox23 midpoint_even_23
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox23,candidate_valid h (FixedTape.midBox ibox23),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox23 83 (FixedTape.rowsAux denominator ibox23 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox23) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_23
private noncomputable def tree22 : TapeTree := .split 1 (((757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree23 tree24
attribute [irreducible] tree22
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox22 1 (757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 : Int) false,decode_split denominator ibox22 1 (757193363545778955816554407876629208339256531550343818865622392189747200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_23 h,accepted_24 h⟩
private noncomputable def tree21 : TapeTree := .split 2 (((865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree22 tree25
attribute [irreducible] tree21
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox21 2 (865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) false,decode_split denominator ibox21 2 (865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_22 h,accepted_25 h⟩
private noncomputable def tree20 : TapeTree := .centered (candidateRows ibox20) (candidateRows (FixedTape.midBox ibox20))
attribute [irreducible] tree20
private theorem sign_20 : 2*denominator*(computed denominator (FixedTape.midBox ibox20)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox20).gradient k).lo.natAbs ((computed denominator ibox20).gradient k).hi.natAbs : Int)*((ibox20 k).hi-(ibox20 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox20
    (computed denominator ibox20) (computed denominator (FixedTape.midBox ibox20))
    (by decide +kernel)
private theorem midpoint_even_20 : ∀ k, 2 ∣ (ibox20 k).lo+(ibox20 k).hi := by decide +kernel
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox20 midpoint_even_20
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox20,candidate_valid h (FixedTape.midBox ibox20),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox20 83 (FixedTape.rowsAux denominator ibox20 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox20) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_20
private noncomputable def tree19 : TapeTree := .face 0 true (candidateRows ibox19) tree20
attribute [irreducible] tree19
private theorem sign_19 : 0 ≤ ((computed denominator ibox19).gradient 0).lo := by decide +kernel
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox19,?_,accepted_20 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox19)).gradient 0).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox19).gradient 0).lo) denominator_positive).2 sign_19
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
private noncomputable def tree17 : TapeTree := .face 0 true (candidateRows ibox17) tree18
attribute [irreducible] tree17
private theorem sign_17 : 0 ≤ ((computed denominator ibox17).gradient 0).lo := by decide +kernel
private theorem accepted_17 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox17) tree17 = true := by
  simp only [tree17,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox17,?_,accepted_18 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox17)).gradient 0).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox17).gradient 0).lo) denominator_positive).2 sign_17
private noncomputable def tree16 : TapeTree := .split 1 (((540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree19
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 1 (540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 : Int) false,decode_split denominator ibox16 1 (540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_17 h,accepted_19 h⟩
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
private noncomputable def tree13 : TapeTree := .split 1 (((540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree14 tree15
attribute [irreducible] tree13
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox13 1 (540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 : Int) false,decode_split denominator ibox13 1 (540852402532699254154681719911878005956611808250245584904015994421248000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_14 h,accepted_15 h⟩
private noncomputable def tree12 : TapeTree := .split 2 (((865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree13 tree16
attribute [irreducible] tree12
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox12 2 (865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) false,decode_split denominator ibox12 2 (865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_13 h,accepted_16 h⟩
private noncomputable def tree11 : TapeTree := .split 1 (((649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree12 tree21
attribute [irreducible] tree11
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox11 1 (649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 : Int) false,decode_split denominator ibox11 1 (649022883039239104985618063894253607147934169900294701884819193305497600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_12 h,accepted_21 h⟩
private noncomputable def tree10 : TapeTree := .centered (candidateRows ibox10) (candidateRows (FixedTape.midBox ibox10))
attribute [irreducible] tree10
private theorem sign_10 : 2*denominator*(computed denominator (FixedTape.midBox ibox10)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox10).gradient k).lo.natAbs ((computed denominator ibox10).gradient k).hi.natAbs : Int)*((ibox10 k).hi-(ibox10 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox10
    (computed denominator ibox10) (computed denominator (FixedTape.midBox ibox10))
    (by decide +kernel)
private theorem midpoint_even_10 : ∀ k, 2 ∣ (ibox10 k).lo+(ibox10 k).hi := by decide +kernel
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox10 midpoint_even_10
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox10,candidate_valid h (FixedTape.midBox ibox10),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox10 83 (FixedTape.rowsAux denominator ibox10 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox10) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_10
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
private noncomputable def tree8 : TapeTree := .split 1 (((324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree9 tree10
attribute [irreducible] tree8
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox8 1 (324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 : Int) false,decode_split denominator ibox8 1 (324511441519619552492809031947126803573967084950147350942409596652748800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_9 h,accepted_10 h⟩
private noncomputable def tree7 : TapeTree := .centered (candidateRows ibox7) (candidateRows (FixedTape.midBox ibox7))
attribute [irreducible] tree7
private theorem sign_7 : 2*denominator*(computed denominator (FixedTape.midBox ibox7)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox7).gradient k).lo.natAbs ((computed denominator ibox7).gradient k).hi.natAbs : Int)*((ibox7 k).hi-(ibox7 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox7
    (computed denominator ibox7) (computed denominator (FixedTape.midBox ibox7))
    (by decide +kernel)
private theorem midpoint_even_7 : ∀ k, 2 ∣ (ibox7 k).lo+(ibox7 k).hi := by decide +kernel
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox7 midpoint_even_7
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox7,candidate_valid h (FixedTape.midBox ibox7),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox7 83 (FixedTape.rowsAux denominator ibox7 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox7) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_7
private noncomputable def tree6 : TapeTree := .split 2 (((865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree8
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 2 (865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) false,decode_split denominator ibox6 2 (865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_7 h,accepted_8 h⟩
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
private noncomputable def tree4 : TapeTree := .face 0 true (candidateRows ibox4) tree5
attribute [irreducible] tree4
private theorem sign_4 : 0 ≤ ((computed denominator ibox4).gradient 0).lo := by decide +kernel
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox4,?_,accepted_5 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox4)).gradient 0).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox4).gradient 0).lo) denominator_positive).2 sign_4
private noncomputable def tree3 : TapeTree := .split 1 (((216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree6
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 : Int) false,decode_split denominator ibox3 1 (216340961013079701661872687964751202382644723300098233961606397768499200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_6 h⟩
private noncomputable def tree2 : TapeTree := .split 1 (((432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree11
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 1 (432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 : Int) false,decode_split denominator ibox2 1 (432681922026159403323745375929502404765289446600196467923212795536998400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_11 h⟩
private noncomputable def tree1 : TapeTree := .split 1 (((865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree2 tree36
attribute [irreducible] tree1
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox1 1 (865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) false,decode_split denominator ibox1 1 (865363844052318806647490751859004809530578893200392935846425591073996800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_2 h,accepted_36 h⟩
private noncomputable def tree0 : TapeTree := .face 3 true (candidateRows ibox0) tree1
attribute [irreducible] tree0
private theorem sign_0 : 0 ≤ ((computed denominator ibox0).gradient 3).lo := by decide +kernel
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
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
private theorem same_expression : tapeExpr tape 83 = e88 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (4791666666666667/5000000000000000 : ℚ) (31/32 : ℚ)) x → eval e88 x ≤ 0 := by
  have hb := h.child_4 tape 83 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell123_high_first_bottom

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell123_high_first_bottom
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((4791666666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((31/32 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 123 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 123 p)
    (hkb : ((31/32 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((4791666666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ bStar), firstResidual (0 : Fin 9) a p r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell123_high_first_bottom.cell_bound h.child_8 h.child_9 (Cell123_high_first_bottom.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell123_high_first_bottom
