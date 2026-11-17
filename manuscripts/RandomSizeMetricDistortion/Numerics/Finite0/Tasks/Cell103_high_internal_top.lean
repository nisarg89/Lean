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
namespace Cell103_high_internal_top
private noncomputable def qValues : Fin 2 → ℚ := ![(1108238307883596870233235205561883159/789416048820057210997690521602962845 : ℚ),(224264314372273834266500000000000000/473649629292034326598614312961777707 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics27.e2 qValues
private noncomputable abbrev e10 : PolyExpr := SharedFiniteSemantics27.e10 qValues
private noncomputable abbrev e14 : PolyExpr := SharedFiniteSemantics27.e14 qValues
private noncomputable abbrev e18 : PolyExpr := SharedFiniteSemantics27.e18 qValues
private noncomputable abbrev e62 : PolyExpr := SharedFiniteSemantics27.e62 qValues
private noncomputable abbrev e123 : PolyExpr := SharedFiniteSemantics27.e123 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics27.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics27.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics27.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics27.node_4 qValues
private noncomputable abbrev node_5 := SharedFiniteSemantics27.node_5 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics27.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics27.node_7 qValues
private noncomputable abbrev node_8 := SharedFiniteSemantics27.node_8 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics27.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics27.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics27.node_11 qValues
private noncomputable abbrev node_12 := SharedFiniteSemantics27.node_12 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics27.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics27.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics27.node_15 qValues
private noncomputable abbrev node_16 := SharedFiniteSemantics27.node_16 qValues
private noncomputable abbrev node_17 := SharedFiniteSemantics27.node_17 qValues
private noncomputable abbrev node_18 := SharedFiniteSemantics27.node_18 qValues
private noncomputable abbrev node_19 := SharedFiniteSemantics27.node_19 qValues
private noncomputable abbrev node_20 := SharedFiniteSemantics27.node_20 qValues
private noncomputable abbrev node_21 := SharedFiniteSemantics27.node_21 qValues
private noncomputable abbrev node_40 := SharedFiniteSemantics27.node_40 qValues
private noncomputable abbrev node_41 := SharedFiniteSemantics27.node_41 qValues
private noncomputable abbrev node_42 := SharedFiniteSemantics27.node_42 qValues
private noncomputable abbrev node_43 := SharedFiniteSemantics27.node_43 qValues
private noncomputable abbrev node_44 := SharedFiniteSemantics27.node_44 qValues
private noncomputable abbrev node_58 := SharedFiniteSemantics27.node_58 qValues
private noncomputable abbrev node_59 := SharedFiniteSemantics27.node_59 qValues
private noncomputable abbrev node_60 := SharedFiniteSemantics27.node_60 qValues
private noncomputable abbrev node_61 := SharedFiniteSemantics27.node_61 qValues
private noncomputable abbrev node_62 := SharedFiniteSemantics27.node_62 qValues
private noncomputable abbrev node_93 := SharedFiniteSemantics27.node_93 qValues
private noncomputable abbrev node_94 := SharedFiniteSemantics27.node_94 qValues
private noncomputable abbrev node_106 := SharedFiniteSemantics27.node_106 qValues
private noncomputable abbrev node_107 := SharedFiniteSemantics27.node_107 qValues
private noncomputable abbrev node_108 := SharedFiniteSemantics27.node_108 qValues
private noncomputable abbrev node_109 := SharedFiniteSemantics27.node_109 qValues
private noncomputable abbrev node_110 := SharedFiniteSemantics27.node_110 qValues
private noncomputable abbrev node_111 := SharedFiniteSemantics27.node_111 qValues
private noncomputable abbrev node_112 := SharedFiniteSemantics27.node_112 qValues
private noncomputable abbrev node_118 := SharedFiniteSemantics27.node_118 qValues
private noncomputable abbrev node_119 := SharedFiniteSemantics27.node_119 qValues
private noncomputable abbrev node_120 := SharedFiniteSemantics27.node_120 qValues
private noncomputable abbrev node_121 := SharedFiniteSemantics27.node_121 qValues
private noncomputable abbrev node_122 := SharedFiniteSemantics27.node_122 qValues
private noncomputable abbrev node_123 := SharedFiniteSemantics27.node_123 qValues
private noncomputable abbrev semantic_H_81 := SharedFiniteSemantics27.semantic_H_81 qValues
private noncomputable abbrev semantic_H_92 := SharedFiniteSemantics27.semantic_H_92 qValues
private noncomputable abbrev semantic_H_105 := SharedFiniteSemantics27.semantic_H_105 qValues
private noncomputable abbrev semantic_psi_39 := SharedFiniteSemantics27.semantic_psi_39 qValues
private noncomputable abbrev semantic_psi_57 := SharedFiniteSemantics27.semantic_psi_57 qValues
private noncomputable abbrev semantic_psi_136 := SharedFiniteSemantics27.semantic_psi_136 qValues
private noncomputable def aPoint (x : Fin 4 → ℝ) : ℝ := bStar+(x 0-bStar)*x 1
private noncomputable def capPoint (x : Fin 4 → ℝ) : ℝ := x 0+(1-x 0)*x 2
private noncomputable def rPoint (x : Fin 4 → ℝ) : ℝ := capPoint x+(1-capPoint x)*x 3
private noncomputable def yPoint (x : Fin 4 → ℝ) : ℝ := aPoint x+capPoint x-x 0
private theorem point_10 (x : Fin 4 → ℝ) : eval e10 x = aPoint x := by
  simp only [node_2,node_3,node_6,node_7,node_8,node_9,node_10] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_18 (x : Fin 4 → ℝ) : eval e18 x = rPoint x := by
  simp only [node_1,node_2,node_4,node_5,node_11,node_12,node_13,node_14,node_15,node_16,node_17,node_18] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_2 (x : Fin 4 → ℝ) : eval e2 x = x 0 := by
  simp only [node_2] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_14 (x : Fin 4 → ℝ) : eval e14 x = capPoint x := by
  simp only [node_1,node_2,node_4,node_11,node_12,node_13,node_14] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_62 (x : Fin 4 → ℝ) : eval e62 x = yPoint x := by
  simp only [node_1,node_2,node_3,node_4,node_6,node_7,node_8,node_9,node_10,node_11,node_12,node_13,node_14,node_61,node_62] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem price_lambda_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceLambda 103 p = ((1108238307883596870233235205561883159/789416048820057210997690521602962845 : ℝ)+(224264314372273834266500000000000000/473649629292034326598614312961777707 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell103,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 103 p = 0 := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell103,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e123 x = (x 0*(1-x 0))*(aPoint x+priceLambda 103 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 103 (x 0)*psiStar (rPoint x)+(cStar-aPoint x-eta (0 : Fin 9)*psiStar (aPoint x))-(cStar-capPoint x-eta (0 : Fin 9)*psiStar (capPoint x))) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_11,node_12,node_15,node_19,node_20,node_21,node_40,node_41,node_42,node_43,node_44,node_58,node_59,node_60,node_93,node_94,node_106,node_107,node_108,node_109,node_110,node_111,node_112,node_118,node_119,node_120,node_121,node_122,node_123,semantic_H_81,semantic_H_92,semantic_H_105,semantic_psi_39,semantic_psi_57,semantic_psi_136,point_10,point_18,point_2,point_14,point_62]
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
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) (ha : bStar < aPoint x) (hA : bStar < capPoint x)
    (hL : lambdaStar (x 0) = priceLambda 103 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 103 (x 0)) :
    (1)*eval e123 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_neg (not_le.mpr ha),if_neg (not_le.mpr hA),hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (3802083333333333/5000000000000000 : ℚ) (3854166666666667/5000000000000000 : ℚ)) x → eval e123 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((3802083333333333/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((3854166666666667/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 103 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 103 p)
    (hkb : ((3854166666666667/5000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((3802083333333333/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : bStar < a) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h7 (3802083333333333/5000000000000000 : ℚ) (3854166666666667/5000000000000000 : ℚ) bStar p a A r hpcell hkb hr.2 hap hcase hpA hAr
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 103 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 103 (x 0) := by simpa only [hxp] using hT
  have hflag : bStar < aPoint x := by simpa only [hax] using hcase
  have hflagA : bStar < capPoint x := by rw [hAx]; exact hcase.trans_le (hap.trans hpA)
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e123 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
  rw [actual_identity hs x hpx hflag hflagA hLx hTx] at hv
  have hscale : 0 < x 0*(1-x 0) := mul_pos hpx.1 (sub_pos.mpr hpx.2)
  have hv : internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x) ≤ 0 := le_of_not_gt (fun hpos => (not_lt_of_ge hv) (mul_pos hscale hpos))
  simpa only [hxp,hax,hAx,hrx] using hv
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
.neg 1,
.add 0 9,
.mul 10 3,
.add 1 11,
.neg 12,
.const (113609/200000 : ℚ),
.neg 8,
.add 14 15,
.const (1085/4818 : ℚ),
.const (19/73 : ℚ),
.mul 18 8,
.mul 8 8,
.const (35/146 : ℚ),
.mul 21 20,
.add 19 22,
.mul 20 20,
.mul 24 24,
.mul 25 25,
.mul 26 26,
.const (1/2 : ℚ),
.mul 28 27,
.add 23 29,
.neg 30,
.add 17 31,
.const (4818/3733 : ℚ),
.mul 33 32,
.const (145513/100000 : ℚ),
.mul 35 34,
.neg 36,
.add 16 37,
.add 14 13,
.mul 18 12,
.mul 12 12,
.mul 21 41,
.add 40 42,
.mul 41 41,
.mul 44 44,
.mul 45 45,
.mul 46 46,
.mul 28 47,
.add 43 48,
.neg 49,
.add 17 50,
.mul 33 51,
.mul 35 52,
.neg 53,
.add 39 54,
.add 8 12,
.add 56 9,
.mul 17 57,
.mul 57 57,
.const (19/146 : ℚ),
.mul 60 59,
.mul 57 59,
.const (35/438 : ℚ),
.mul 63 62,
.add 61 64,
.mul 59 59,
.mul 66 66,
.mul 67 67,
.mul 68 68,
.mul 57 69,
.const (1/66 : ℚ),
.mul 71 70,
.add 65 72,
.neg 73,
.add 58 74,
.mul 33 75,
.mul 17 8,
.mul 60 20,
.mul 8 20,
.mul 63 79,
.add 78 80,
.mul 8 27,
.mul 71 82,
.add 81 83,
.neg 84,
.add 77 85,
.mul 33 86,
.neg 87,
.add 76 88,
.mul 17 12,
.mul 60 41,
.mul 12 41,
.mul 63 92,
.add 91 93,
.mul 12 47,
.mul 71 95,
.add 94 96,
.neg 97,
.add 90 98,
.mul 33 99,
.neg 100,
.add 89 101,
.const (1108238307883596870233235205561883159/789416048820057210997690521602962845 : ℚ),
.const (224264314372273834266500000000000000/473649629292034326598614312961777707 : ℚ),
.mul 104 1,
.add 103 105,
.mul 1 10,
.add 8 38,
.neg 55,
.add 108 109,
.mul 110 107,
.mul 106 102,
.add 111 112]
private noncomputable def ssaQVals : Fin 15 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(-2840189/5000000 : ℚ),(113609/200000 : ℚ),(1085/4818 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ),(4818/3733 : ℚ),(145513/100000 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(1108238307883596870233235205561883159/789416048820057210997690521602962845 : ℚ),(224264314372273834266500000000000000/473649629292034326598614312961777707 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_dd21b86a37681a92.p114 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_dd21b86a37681a92.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 113 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_dd21b86a37681a92.ssa_matches ssaQVals D B

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
private noncomputable def denominator : Int := 2045255791839832148552166545478886515650004707208037033681759579511193600000000000000000000000
private theorem denominator_positive : 0 < denominator := by decide +kernel
private noncomputable def candidateRows (B : Fin 4 → FixedTape.I) : List TapeBounds :=
  (FixedTape.rowsAux denominator B [] tape).map (FixedTape.decodeRow denominator)
private theorem root_in_range : 113 < tape.length := by decide +kernel
private theorem references_valid : tapeRefsValidAux 0 tape = true := by decide +kernel
private theorem candidate_valid (h : Needs) (B : Fin 4 → FixedTape.I) :
    tapeCheck (FixedTape.decodeBox denominator B) tape (candidateRows B) = true :=
  h.child_10.1 denominator denominator_positive B tape references_valid
private theorem candidate_root (B : Fin 4 → FixedTape.I) :
    (candidateRows B).getD 113 zeroTapeBounds = FixedTape.decodeRow denominator (computed denominator B) := by
  unfold candidateRows
  rw [←decode_zeroRow denominator,List.getD_map,ssa_matches]
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨1555246591711538893277823854635760051131088047513677117695190866384167887882694699253760000000,1576551339543204084192681168128784925957981660398629590130003489742347312117305300746240000000⟩,⟨0,2045255791839832148552166545478886515650004707208037033681759579511193600000000000000000000000⟩,⟨0,2045255791839832148552166545478886515650004707208037033681759579511193600000000000000000000000⟩,⟨0,2045255791839832148552166545478886515650004707208037033681759579511193600000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 3 true
private noncomputable def ibox2 : Fin 4 → FixedTape.I := splitI ibox1 2 1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 1 1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 2 511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 1 511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox4 1 511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 true
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 2 255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox6 2 255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox3 2 511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox9 1 511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 false
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox10 2 766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 false
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox10 2 766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 true
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox12 1 255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 false
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox12 1 255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 true
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox9 1 511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 true
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox15 2 766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 false
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 1 766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox16 1 766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox15 2 766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 1 766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox19 1 766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 true
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox2 1 1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 true
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox22 2 511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 false
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox23 1 1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 false
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox24 1 1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 false
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox25 2 255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 false
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox25 2 255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 true
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox24 1 1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 true
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox28 2 255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 false
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox28 2 255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 true
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox23 1 1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 true
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox31 1 1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 false
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox32 2 255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 false
private noncomputable def ibox34 : Fin 4 → FixedTape.I := faceI ibox33 1 true
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox32 2 255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 true
private noncomputable def ibox36 : Fin 4 → FixedTape.I := splitI ibox35 1 1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 false
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox35 1 1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 true
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox37 2 383485460969968527853531227277291221684375882601506943815329921158348800000000000000000000000 false
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox37 2 383485460969968527853531227277291221684375882601506943815329921158348800000000000000000000000 true
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox31 1 1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 true
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox40 2 255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 false
private noncomputable def ibox42 : Fin 4 → FixedTape.I := faceI ibox41 1 true
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox42 2 127828486989989509284510409092430407228125294200502314605109973719449600000000000000000000000 false
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox43 2 63914243494994754642255204546215203614062647100251157302554986859724800000000000000000000000 false
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox44 0 1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 false
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox45 2 31957121747497377321127602273107601807031323550125578651277493429862400000000000000000000000 false
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox46 0 1560572778669455191006538183009016269837811450734915235803894022223712743941347349626880000000 false
private noncomputable def ibox48 : Fin 4 → FixedTape.I := faceI ibox47 2 false
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox48 0 1557909685190497042142181018822388160484449749124296176749542444303940315912021024440320000000 false
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox48 0 1557909685190497042142181018822388160484449749124296176749542444303940315912021024440320000000 true
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox46 0 1560572778669455191006538183009016269837811450734915235803894022223712743941347349626880000000 true
private noncomputable def ibox52 : Fin 4 → FixedTape.I := faceI ibox51 2 false
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox52 0 1563235872148413339870895347195644379191173152345534294858245600143485171970673674813440000000 false
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox52 0 1563235872148413339870895347195644379191173152345534294858245600143485171970673674813440000000 true
private noncomputable def ibox55 : Fin 4 → FixedTape.I := splitI ibox45 2 31957121747497377321127602273107601807031323550125578651277493429862400000000000000000000000 true
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox55 0 1560572778669455191006538183009016269837811450734915235803894022223712743941347349626880000000 false
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox55 0 1560572778669455191006538183009016269837811450734915235803894022223712743941347349626880000000 true
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox44 0 1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 true
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox58 2 31957121747497377321127602273107601807031323550125578651277493429862400000000000000000000000 false
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox59 0 1571225152585287786463966839755528707251258257177391472021300333902802456058652650373120000000 false
private noncomputable def ibox61 : Fin 4 → FixedTape.I := faceI ibox60 2 false
private noncomputable def ibox62 : Fin 4 → FixedTape.I := splitI ibox61 0 1568562059106329637599609675568900597897896555566772412966948755983030028029326325186560000000 false
private noncomputable def ibox63 : Fin 4 → FixedTape.I := splitI ibox61 0 1568562059106329637599609675568900597897896555566772412966948755983030028029326325186560000000 true
private noncomputable def ibox64 : Fin 4 → FixedTape.I := splitI ibox59 0 1571225152585287786463966839755528707251258257177391472021300333902802456058652650373120000000 true
private noncomputable def ibox65 : Fin 4 → FixedTape.I := faceI ibox64 2 false
private noncomputable def ibox66 : Fin 4 → FixedTape.I := splitI ibox65 0 1573888246064245935328324003942156816604619958788010531075651911822574884087978975559680000000 false
private noncomputable def ibox67 : Fin 4 → FixedTape.I := splitI ibox65 0 1573888246064245935328324003942156816604619958788010531075651911822574884087978975559680000000 true
private noncomputable def ibox68 : Fin 4 → FixedTape.I := splitI ibox58 2 31957121747497377321127602273107601807031323550125578651277493429862400000000000000000000000 true
private noncomputable def ibox69 : Fin 4 → FixedTape.I := splitI ibox68 0 1571225152585287786463966839755528707251258257177391472021300333902802456058652650373120000000 false
private noncomputable def ibox70 : Fin 4 → FixedTape.I := splitI ibox68 0 1571225152585287786463966839755528707251258257177391472021300333902802456058652650373120000000 true
private noncomputable def ibox71 : Fin 4 → FixedTape.I := splitI ibox43 2 63914243494994754642255204546215203614062647100251157302554986859724800000000000000000000000 true
private noncomputable def ibox72 : Fin 4 → FixedTape.I := splitI ibox71 0 1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 false
private noncomputable def ibox73 : Fin 4 → FixedTape.I := splitI ibox72 2 95871365242492131963382806819322805421093970650376735953832480289587200000000000000000000000 false
private noncomputable def ibox74 : Fin 4 → FixedTape.I := splitI ibox73 0 1560572778669455191006538183009016269837811450734915235803894022223712743941347349626880000000 false
private noncomputable def ibox75 : Fin 4 → FixedTape.I := splitI ibox73 0 1560572778669455191006538183009016269837811450734915235803894022223712743941347349626880000000 true
private noncomputable def ibox76 : Fin 4 → FixedTape.I := splitI ibox72 2 95871365242492131963382806819322805421093970650376735953832480289587200000000000000000000000 true
private noncomputable def ibox77 : Fin 4 → FixedTape.I := splitI ibox71 0 1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 true
private noncomputable def ibox78 : Fin 4 → FixedTape.I := splitI ibox77 2 95871365242492131963382806819322805421093970650376735953832480289587200000000000000000000000 false
private noncomputable def ibox79 : Fin 4 → FixedTape.I := splitI ibox78 0 1571225152585287786463966839755528707251258257177391472021300333902802456058652650373120000000 false
private noncomputable def ibox80 : Fin 4 → FixedTape.I := splitI ibox78 0 1571225152585287786463966839755528707251258257177391472021300333902802456058652650373120000000 true
private noncomputable def ibox81 : Fin 4 → FixedTape.I := splitI ibox77 2 95871365242492131963382806819322805421093970650376735953832480289587200000000000000000000000 true
private noncomputable def ibox82 : Fin 4 → FixedTape.I := splitI ibox42 2 127828486989989509284510409092430407228125294200502314605109973719449600000000000000000000000 true
private noncomputable def ibox83 : Fin 4 → FixedTape.I := splitI ibox82 2 191742730484984263926765613638645610842187941300753471907664960579174400000000000000000000000 false
private noncomputable def ibox84 : Fin 4 → FixedTape.I := splitI ibox83 0 1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 false
private noncomputable def ibox85 : Fin 4 → FixedTape.I := splitI ibox83 0 1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 true
private noncomputable def ibox86 : Fin 4 → FixedTape.I := splitI ibox82 2 191742730484984263926765613638645610842187941300753471907664960579174400000000000000000000000 true
private noncomputable def ibox87 : Fin 4 → FixedTape.I := splitI ibox86 0 1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 false
private noncomputable def ibox88 : Fin 4 → FixedTape.I := splitI ibox86 0 1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 true
private noncomputable def ibox89 : Fin 4 → FixedTape.I := splitI ibox40 2 255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 true
private noncomputable def ibox90 : Fin 4 → FixedTape.I := splitI ibox89 1 1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 false
private noncomputable def ibox91 : Fin 4 → FixedTape.I := splitI ibox90 2 383485460969968527853531227277291221684375882601506943815329921158348800000000000000000000000 false
private noncomputable def ibox92 : Fin 4 → FixedTape.I := faceI ibox91 1 true
private noncomputable def ibox93 : Fin 4 → FixedTape.I := splitI ibox90 2 383485460969968527853531227277291221684375882601506943815329921158348800000000000000000000000 true
private noncomputable def ibox94 : Fin 4 → FixedTape.I := splitI ibox93 0 1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 false
private noncomputable def ibox95 : Fin 4 → FixedTape.I := splitI ibox93 0 1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 true
private noncomputable def ibox96 : Fin 4 → FixedTape.I := splitI ibox89 1 1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 true
private noncomputable def ibox97 : Fin 4 → FixedTape.I := splitI ibox96 2 383485460969968527853531227277291221684375882601506943815329921158348800000000000000000000000 false
private noncomputable def ibox98 : Fin 4 → FixedTape.I := faceI ibox97 1 true
private noncomputable def ibox99 : Fin 4 → FixedTape.I := splitI ibox98 2 319571217474973773211276022731076018070313235501255786512774934298624000000000000000000000000 false
private noncomputable def ibox100 : Fin 4 → FixedTape.I := splitI ibox99 0 1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 false
private noncomputable def ibox101 : Fin 4 → FixedTape.I := splitI ibox99 0 1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 true
private noncomputable def ibox102 : Fin 4 → FixedTape.I := splitI ibox98 2 319571217474973773211276022731076018070313235501255786512774934298624000000000000000000000000 true
private noncomputable def ibox103 : Fin 4 → FixedTape.I := splitI ibox96 2 383485460969968527853531227277291221684375882601506943815329921158348800000000000000000000000 true
private noncomputable def ibox104 : Fin 4 → FixedTape.I := splitI ibox103 0 1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 false
private noncomputable def ibox105 : Fin 4 → FixedTape.I := faceI ibox104 1 true
private noncomputable def ibox106 : Fin 4 → FixedTape.I := splitI ibox103 0 1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 true
private noncomputable def ibox107 : Fin 4 → FixedTape.I := faceI ibox106 1 true
private noncomputable def ibox108 : Fin 4 → FixedTape.I := splitI ibox22 2 511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 true
private noncomputable def ibox109 : Fin 4 → FixedTape.I := splitI ibox108 1 1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 false
private noncomputable def ibox110 : Fin 4 → FixedTape.I := splitI ibox109 2 766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 false
private noncomputable def ibox111 : Fin 4 → FixedTape.I := splitI ibox110 1 1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 false
private noncomputable def ibox112 : Fin 4 → FixedTape.I := splitI ibox110 1 1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 true
private noncomputable def ibox113 : Fin 4 → FixedTape.I := splitI ibox112 1 1406113356889884602129614500016734479509378236205525460656209710913945600000000000000000000000 false
private noncomputable def ibox114 : Fin 4 → FixedTape.I := splitI ibox112 1 1406113356889884602129614500016734479509378236205525460656209710913945600000000000000000000000 true
private noncomputable def ibox115 : Fin 4 → FixedTape.I := splitI ibox109 2 766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 true
private noncomputable def ibox116 : Fin 4 → FixedTape.I := splitI ibox115 1 1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 false
private noncomputable def ibox117 : Fin 4 → FixedTape.I := splitI ibox115 1 1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 true
private noncomputable def ibox118 : Fin 4 → FixedTape.I := splitI ibox117 2 894799408929926564991572863647012850596877059403516202235769816036147200000000000000000000000 false
private noncomputable def ibox119 : Fin 4 → FixedTape.I := splitI ibox117 2 894799408929926564991572863647012850596877059403516202235769816036147200000000000000000000000 true
private noncomputable def ibox120 : Fin 4 → FixedTape.I := splitI ibox108 1 1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 true
private noncomputable def ibox121 : Fin 4 → FixedTape.I := splitI ibox120 2 766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 false
private noncomputable def ibox122 : Fin 4 → FixedTape.I := splitI ibox121 1 1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 false
private noncomputable def ibox123 : Fin 4 → FixedTape.I := splitI ibox122 1 1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 false
private noncomputable def ibox124 : Fin 4 → FixedTape.I := splitI ibox122 1 1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 true
private noncomputable def ibox125 : Fin 4 → FixedTape.I := splitI ibox124 2 639142434949947546422552045462152036140626471002511573025549868597248000000000000000000000000 false
private noncomputable def ibox126 : Fin 4 → FixedTape.I := splitI ibox124 2 639142434949947546422552045462152036140626471002511573025549868597248000000000000000000000000 true
private noncomputable def ibox127 : Fin 4 → FixedTape.I := splitI ibox121 1 1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 true
private noncomputable def ibox128 : Fin 4 → FixedTape.I := splitI ibox127 2 639142434949947546422552045462152036140626471002511573025549868597248000000000000000000000000 false
private noncomputable def ibox129 : Fin 4 → FixedTape.I := splitI ibox128 1 1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 false
private noncomputable def ibox130 : Fin 4 → FixedTape.I := splitI ibox128 1 1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 true
private noncomputable def ibox131 : Fin 4 → FixedTape.I := splitI ibox130 0 1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 false
private noncomputable def ibox132 : Fin 4 → FixedTape.I := splitI ibox130 0 1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 true
private noncomputable def ibox133 : Fin 4 → FixedTape.I := splitI ibox127 2 639142434949947546422552045462152036140626471002511573025549868597248000000000000000000000000 true
private noncomputable def ibox134 : Fin 4 → FixedTape.I := splitI ibox133 1 1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 false
private noncomputable def ibox135 : Fin 4 → FixedTape.I := splitI ibox133 1 1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 true
private noncomputable def ibox136 : Fin 4 → FixedTape.I := splitI ibox135 0 1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 false
private noncomputable def ibox137 : Fin 4 → FixedTape.I := splitI ibox135 0 1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 true
private noncomputable def ibox138 : Fin 4 → FixedTape.I := splitI ibox120 2 766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 true
private noncomputable def ibox139 : Fin 4 → FixedTape.I := splitI ibox138 1 1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 false
private noncomputable def ibox140 : Fin 4 → FixedTape.I := splitI ibox139 2 894799408929926564991572863647012850596877059403516202235769816036147200000000000000000000000 false
private noncomputable def ibox141 : Fin 4 → FixedTape.I := splitI ibox139 2 894799408929926564991572863647012850596877059403516202235769816036147200000000000000000000000 true
private noncomputable def ibox142 : Fin 4 → FixedTape.I := splitI ibox138 1 1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 true
private noncomputable def ibox143 : Fin 4 → FixedTape.I := splitI ibox142 2 894799408929926564991572863647012850596877059403516202235769816036147200000000000000000000000 false
private noncomputable def ibox144 : Fin 4 → FixedTape.I := splitI ibox143 1 1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 false
private noncomputable def ibox145 : Fin 4 → FixedTape.I := splitI ibox143 1 1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 true
private noncomputable def ibox146 : Fin 4 → FixedTape.I := splitI ibox145 2 830885165434931810349317659100797646982814412303265044933214829176422400000000000000000000000 false
private noncomputable def ibox147 : Fin 4 → FixedTape.I := splitI ibox145 2 830885165434931810349317659100797646982814412303265044933214829176422400000000000000000000000 true
private noncomputable def ibox148 : Fin 4 → FixedTape.I := splitI ibox142 2 894799408929926564991572863647012850596877059403516202235769816036147200000000000000000000000 true
private noncomputable def ibox149 : Fin 4 → FixedTape.I := splitI ibox148 0 1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 false
private noncomputable def ibox150 : Fin 4 → FixedTape.I := splitI ibox148 0 1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 true
private noncomputable def ibox151 : Fin 4 → FixedTape.I := splitI ibox1 2 1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 true
private noncomputable def ibox152 : Fin 4 → FixedTape.I := splitI ibox151 2 1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 false
private noncomputable def ibox153 : Fin 4 → FixedTape.I := splitI ibox152 1 1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 false
private noncomputable def ibox154 : Fin 4 → FixedTape.I := splitI ibox153 2 1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 false
private noncomputable def ibox155 : Fin 4 → FixedTape.I := splitI ibox154 1 511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 false
private noncomputable def ibox156 : Fin 4 → FixedTape.I := splitI ibox155 2 1150456382909905583560593681831873665053127647804520831445989763475046400000000000000000000000 false
private noncomputable def ibox157 : Fin 4 → FixedTape.I := splitI ibox155 2 1150456382909905583560593681831873665053127647804520831445989763475046400000000000000000000000 true
private noncomputable def ibox158 : Fin 4 → FixedTape.I := splitI ibox154 1 511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 true
private noncomputable def ibox159 : Fin 4 → FixedTape.I := splitI ibox158 2 1150456382909905583560593681831873665053127647804520831445989763475046400000000000000000000000 false
private noncomputable def ibox160 : Fin 4 → FixedTape.I := splitI ibox158 2 1150456382909905583560593681831873665053127647804520831445989763475046400000000000000000000000 true
private noncomputable def ibox161 : Fin 4 → FixedTape.I := splitI ibox160 1 766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 false
private noncomputable def ibox162 : Fin 4 → FixedTape.I := splitI ibox160 1 766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 true
private noncomputable def ibox163 : Fin 4 → FixedTape.I := splitI ibox153 2 1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 true
private noncomputable def ibox164 : Fin 4 → FixedTape.I := splitI ibox163 2 1406113356889884602129614500016734479509378236205525460656209710913945600000000000000000000000 false
private noncomputable def ibox165 : Fin 4 → FixedTape.I := splitI ibox164 1 511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 false
private noncomputable def ibox166 : Fin 4 → FixedTape.I := splitI ibox165 1 255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 false
private noncomputable def ibox167 : Fin 4 → FixedTape.I := splitI ibox165 1 255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 true
private noncomputable def ibox168 : Fin 4 → FixedTape.I := splitI ibox164 1 511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 true
private noncomputable def ibox169 : Fin 4 → FixedTape.I := splitI ibox168 1 766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 false
private noncomputable def ibox170 : Fin 4 → FixedTape.I := splitI ibox168 1 766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 true
private noncomputable def ibox171 : Fin 4 → FixedTape.I := splitI ibox163 2 1406113356889884602129614500016734479509378236205525460656209710913945600000000000000000000000 true
private noncomputable def ibox172 : Fin 4 → FixedTape.I := splitI ibox171 1 511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 false
private noncomputable def ibox173 : Fin 4 → FixedTape.I := splitI ibox172 2 1470027600384879356771869704562949683123440883305776617958764697773670400000000000000000000000 false
private noncomputable def ibox174 : Fin 4 → FixedTape.I := splitI ibox172 2 1470027600384879356771869704562949683123440883305776617958764697773670400000000000000000000000 true
private noncomputable def ibox175 : Fin 4 → FixedTape.I := splitI ibox171 1 511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 true
private noncomputable def ibox176 : Fin 4 → FixedTape.I := splitI ibox175 2 1470027600384879356771869704562949683123440883305776617958764697773670400000000000000000000000 false
private noncomputable def ibox177 : Fin 4 → FixedTape.I := splitI ibox175 2 1470027600384879356771869704562949683123440883305776617958764697773670400000000000000000000000 true
private noncomputable def ibox178 : Fin 4 → FixedTape.I := splitI ibox152 1 1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 true
private noncomputable def ibox179 : Fin 4 → FixedTape.I := splitI ibox178 2 1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 false
private noncomputable def ibox180 : Fin 4 → FixedTape.I := splitI ibox179 1 1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 false
private noncomputable def ibox181 : Fin 4 → FixedTape.I := splitI ibox180 2 1150456382909905583560593681831873665053127647804520831445989763475046400000000000000000000000 false
private noncomputable def ibox182 : Fin 4 → FixedTape.I := splitI ibox181 1 1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 false
private noncomputable def ibox183 : Fin 4 → FixedTape.I := splitI ibox181 1 1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 true
private noncomputable def ibox184 : Fin 4 → FixedTape.I := splitI ibox180 2 1150456382909905583560593681831873665053127647804520831445989763475046400000000000000000000000 true
private noncomputable def ibox185 : Fin 4 → FixedTape.I := splitI ibox184 1 1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 false
private noncomputable def ibox186 : Fin 4 → FixedTape.I := splitI ibox184 1 1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 true
private noncomputable def ibox187 : Fin 4 → FixedTape.I := splitI ibox179 1 1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 true
private noncomputable def ibox188 : Fin 4 → FixedTape.I := splitI ibox187 2 1150456382909905583560593681831873665053127647804520831445989763475046400000000000000000000000 false
private noncomputable def ibox189 : Fin 4 → FixedTape.I := splitI ibox188 1 1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 false
private noncomputable def ibox190 : Fin 4 → FixedTape.I := splitI ibox188 1 1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 true
private noncomputable def ibox191 : Fin 4 → FixedTape.I := splitI ibox190 2 1086542139414910828918338477285658461439065000704269674143434776615321600000000000000000000000 false
private noncomputable def ibox192 : Fin 4 → FixedTape.I := splitI ibox190 2 1086542139414910828918338477285658461439065000704269674143434776615321600000000000000000000000 true
private noncomputable def ibox193 : Fin 4 → FixedTape.I := splitI ibox187 2 1150456382909905583560593681831873665053127647804520831445989763475046400000000000000000000000 true
private noncomputable def ibox194 : Fin 4 → FixedTape.I := splitI ibox193 1 1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 false
private noncomputable def ibox195 : Fin 4 → FixedTape.I := splitI ibox193 1 1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 true
private noncomputable def ibox196 : Fin 4 → FixedTape.I := splitI ibox178 2 1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 true
private noncomputable def ibox197 : Fin 4 → FixedTape.I := splitI ibox196 1 1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 false
private noncomputable def ibox198 : Fin 4 → FixedTape.I := splitI ibox197 2 1406113356889884602129614500016734479509378236205525460656209710913945600000000000000000000000 false
private noncomputable def ibox199 : Fin 4 → FixedTape.I := splitI ibox198 1 1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 false
private noncomputable def ibox200 : Fin 4 → FixedTape.I := splitI ibox198 1 1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 true
private noncomputable def ibox201 : Fin 4 → FixedTape.I := splitI ibox197 2 1406113356889884602129614500016734479509378236205525460656209710913945600000000000000000000000 true
private noncomputable def ibox202 : Fin 4 → FixedTape.I := splitI ibox201 2 1470027600384879356771869704562949683123440883305776617958764697773670400000000000000000000000 false
private noncomputable def ibox203 : Fin 4 → FixedTape.I := splitI ibox201 2 1470027600384879356771869704562949683123440883305776617958764697773670400000000000000000000000 true
private noncomputable def ibox204 : Fin 4 → FixedTape.I := splitI ibox196 1 1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 true
private noncomputable def ibox205 : Fin 4 → FixedTape.I := splitI ibox204 2 1406113356889884602129614500016734479509378236205525460656209710913945600000000000000000000000 false
private noncomputable def ibox206 : Fin 4 → FixedTape.I := splitI ibox205 1 1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 false
private noncomputable def ibox207 : Fin 4 → FixedTape.I := splitI ibox205 1 1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 true
private noncomputable def ibox208 : Fin 4 → FixedTape.I := splitI ibox204 2 1406113356889884602129614500016734479509378236205525460656209710913945600000000000000000000000 true
private noncomputable def ibox209 : Fin 4 → FixedTape.I := splitI ibox208 1 1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 false
private noncomputable def ibox210 : Fin 4 → FixedTape.I := splitI ibox208 1 1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 true
private noncomputable def ibox211 : Fin 4 → FixedTape.I := splitI ibox151 2 1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 true
private noncomputable def ibox212 : Fin 4 → FixedTape.I := splitI ibox211 2 1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 false
private noncomputable def ibox213 : Fin 4 → FixedTape.I := splitI ibox212 1 1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 false
private noncomputable def ibox214 : Fin 4 → FixedTape.I := splitI ibox213 2 1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 false
private noncomputable def ibox215 : Fin 4 → FixedTape.I := splitI ibox214 1 511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 false
private noncomputable def ibox216 : Fin 4 → FixedTape.I := splitI ibox215 2 1597856087374868866056380113655380090351566177506278932563874671493120000000000000000000000000 false
private noncomputable def ibox217 : Fin 4 → FixedTape.I := splitI ibox215 2 1597856087374868866056380113655380090351566177506278932563874671493120000000000000000000000000 true
private noncomputable def ibox218 : Fin 4 → FixedTape.I := splitI ibox214 1 511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 true
private noncomputable def ibox219 : Fin 4 → FixedTape.I := splitI ibox218 2 1597856087374868866056380113655380090351566177506278932563874671493120000000000000000000000000 false
private noncomputable def ibox220 : Fin 4 → FixedTape.I := splitI ibox218 2 1597856087374868866056380113655380090351566177506278932563874671493120000000000000000000000000 true
private noncomputable def ibox221 : Fin 4 → FixedTape.I := splitI ibox213 2 1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 true
private noncomputable def ibox222 : Fin 4 → FixedTape.I := splitI ibox221 2 1725684574364858375340890522747810497579691471706781247168984645212569600000000000000000000000 false
private noncomputable def ibox223 : Fin 4 → FixedTape.I := splitI ibox221 2 1725684574364858375340890522747810497579691471706781247168984645212569600000000000000000000000 true
private noncomputable def ibox224 : Fin 4 → FixedTape.I := splitI ibox212 1 1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 true
private noncomputable def ibox225 : Fin 4 → FixedTape.I := splitI ibox224 1 1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 false
private noncomputable def ibox226 : Fin 4 → FixedTape.I := splitI ibox225 2 1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 false
private noncomputable def ibox227 : Fin 4 → FixedTape.I := splitI ibox226 2 1597856087374868866056380113655380090351566177506278932563874671493120000000000000000000000000 false
private noncomputable def ibox228 : Fin 4 → FixedTape.I := splitI ibox226 2 1597856087374868866056380113655380090351566177506278932563874671493120000000000000000000000000 true
private noncomputable def ibox229 : Fin 4 → FixedTape.I := splitI ibox225 2 1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 true
private noncomputable def ibox230 : Fin 4 → FixedTape.I := splitI ibox224 1 1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 true
private noncomputable def ibox231 : Fin 4 → FixedTape.I := splitI ibox230 2 1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 false
private noncomputable def ibox232 : Fin 4 → FixedTape.I := faceI ibox231 2 false
private noncomputable def ibox233 : Fin 4 → FixedTape.I := splitI ibox230 2 1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 true
private noncomputable def ibox234 : Fin 4 → FixedTape.I := faceI ibox233 2 false
private noncomputable def ibox235 : Fin 4 → FixedTape.I := splitI ibox211 2 1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 true
private noncomputable def ibox236 : Fin 4 → FixedTape.I := splitI ibox235 1 1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 false
private noncomputable def ibox237 : Fin 4 → FixedTape.I := splitI ibox236 2 1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 false
private noncomputable def ibox238 : Fin 4 → FixedTape.I := faceI ibox237 2 false
private noncomputable def ibox239 : Fin 4 → FixedTape.I := splitI ibox236 2 1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 true
private noncomputable def ibox240 : Fin 4 → FixedTape.I := splitI ibox235 1 1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 true
private noncomputable def ibox241 : Fin 4 → FixedTape.I := splitI ibox240 2 1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 false
private noncomputable def ibox242 : Fin 4 → FixedTape.I := faceI ibox241 2 false
private noncomputable def ibox243 : Fin 4 → FixedTape.I := splitI ibox242 1 1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 false
private noncomputable def ibox244 : Fin 4 → FixedTape.I := splitI ibox242 1 1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 true
private noncomputable def ibox245 : Fin 4 → FixedTape.I := splitI ibox240 2 1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 true
private noncomputable def ibox246 : Fin 4 → FixedTape.I := faceI ibox245 2 false
private noncomputable def ibox247 : Fin 4 → FixedTape.I := splitI ibox246 1 1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 false
private noncomputable def ibox248 : Fin 4 → FixedTape.I := splitI ibox246 1 1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 true
private noncomputable def tree248 : TapeTree := .centered (candidateRows ibox248) (candidateRows (FixedTape.midBox ibox248))
attribute [irreducible] tree248
private theorem sign_248 : 2*denominator*(computed denominator (FixedTape.midBox ibox248)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox248).gradient k).lo.natAbs ((computed denominator ibox248).gradient k).hi.natAbs : Int)*((ibox248 k).hi-(ibox248 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox248
    (computed denominator ibox248) (computed denominator (FixedTape.midBox ibox248))
    (by decide +kernel)
private theorem midpoint_even_248 : ∀ k, 2 ∣ (ibox248 k).lo+(ibox248 k).hi := by decide +kernel
private theorem accepted_248 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox248) tree248 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox248 midpoint_even_248
  simp only [tree248,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox248,candidate_valid h (FixedTape.midBox ibox248),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox248 113 (FixedTape.rowsAux denominator ibox248 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox248) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_248
private noncomputable def tree247 : TapeTree := .centered (candidateRows ibox247) (candidateRows (FixedTape.midBox ibox247))
attribute [irreducible] tree247
private theorem sign_247 : 2*denominator*(computed denominator (FixedTape.midBox ibox247)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox247).gradient k).lo.natAbs ((computed denominator ibox247).gradient k).hi.natAbs : Int)*((ibox247 k).hi-(ibox247 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox247
    (computed denominator ibox247) (computed denominator (FixedTape.midBox ibox247))
    (by decide +kernel)
private theorem midpoint_even_247 : ∀ k, 2 ∣ (ibox247 k).lo+(ibox247 k).hi := by decide +kernel
private theorem accepted_247 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox247) tree247 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox247 midpoint_even_247
  simp only [tree247,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox247,candidate_valid h (FixedTape.midBox ibox247),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox247 113 (FixedTape.rowsAux denominator ibox247 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox247) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_247
private noncomputable def tree246 : TapeTree := .split 1 (((1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree247 tree248
attribute [irreducible] tree246
private theorem accepted_246 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox246) tree246 = true := by
  simp only [tree246,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox246 1 (1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) false,decode_split denominator ibox246 1 (1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_247 h,accepted_248 h⟩
private noncomputable def tree245 : TapeTree := .face 2 false (candidateRows ibox245) tree246
attribute [irreducible] tree245
private theorem sign_245 : ((computed denominator ibox245).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_245 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox245) tree245 = true := by
  simp only [tree245,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox245,?_,accepted_246 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox245)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox245).gradient 2).hi) denominator_positive).1 sign_245
private noncomputable def tree244 : TapeTree := .centered (candidateRows ibox244) (candidateRows (FixedTape.midBox ibox244))
attribute [irreducible] tree244
private theorem sign_244 : 2*denominator*(computed denominator (FixedTape.midBox ibox244)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox244).gradient k).lo.natAbs ((computed denominator ibox244).gradient k).hi.natAbs : Int)*((ibox244 k).hi-(ibox244 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox244
    (computed denominator ibox244) (computed denominator (FixedTape.midBox ibox244))
    (by decide +kernel)
private theorem midpoint_even_244 : ∀ k, 2 ∣ (ibox244 k).lo+(ibox244 k).hi := by decide +kernel
private theorem accepted_244 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox244) tree244 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox244 midpoint_even_244
  simp only [tree244,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox244,candidate_valid h (FixedTape.midBox ibox244),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox244 113 (FixedTape.rowsAux denominator ibox244 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox244) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_244
private noncomputable def tree243 : TapeTree := .centered (candidateRows ibox243) (candidateRows (FixedTape.midBox ibox243))
attribute [irreducible] tree243
private theorem sign_243 : 2*denominator*(computed denominator (FixedTape.midBox ibox243)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox243).gradient k).lo.natAbs ((computed denominator ibox243).gradient k).hi.natAbs : Int)*((ibox243 k).hi-(ibox243 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox243
    (computed denominator ibox243) (computed denominator (FixedTape.midBox ibox243))
    (by decide +kernel)
private theorem midpoint_even_243 : ∀ k, 2 ∣ (ibox243 k).lo+(ibox243 k).hi := by decide +kernel
private theorem accepted_243 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox243) tree243 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox243 midpoint_even_243
  simp only [tree243,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox243,candidate_valid h (FixedTape.midBox ibox243),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox243 113 (FixedTape.rowsAux denominator ibox243 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox243) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_243
private noncomputable def tree242 : TapeTree := .split 1 (((1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree243 tree244
attribute [irreducible] tree242
private theorem accepted_242 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox242) tree242 = true := by
  simp only [tree242,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox242 1 (1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) false,decode_split denominator ibox242 1 (1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_243 h,accepted_244 h⟩
private noncomputable def tree241 : TapeTree := .face 2 false (candidateRows ibox241) tree242
attribute [irreducible] tree241
private theorem sign_241 : ((computed denominator ibox241).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_241 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox241) tree241 = true := by
  simp only [tree241,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox241,?_,accepted_242 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox241)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox241).gradient 2).hi) denominator_positive).1 sign_241
private noncomputable def tree240 : TapeTree := .split 2 (((1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree241 tree245
attribute [irreducible] tree240
private theorem accepted_240 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox240) tree240 = true := by
  simp only [tree240,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox240 2 (1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 : Int) false,decode_split denominator ibox240 2 (1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_241 h,accepted_245 h⟩
private noncomputable def tree239 : TapeTree := .centered (candidateRows ibox239) (candidateRows (FixedTape.midBox ibox239))
attribute [irreducible] tree239
private theorem sign_239 : 2*denominator*(computed denominator (FixedTape.midBox ibox239)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox239).gradient k).lo.natAbs ((computed denominator ibox239).gradient k).hi.natAbs : Int)*((ibox239 k).hi-(ibox239 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox239
    (computed denominator ibox239) (computed denominator (FixedTape.midBox ibox239))
    (by decide +kernel)
private theorem midpoint_even_239 : ∀ k, 2 ∣ (ibox239 k).lo+(ibox239 k).hi := by decide +kernel
private theorem accepted_239 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox239) tree239 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox239 midpoint_even_239
  simp only [tree239,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox239,candidate_valid h (FixedTape.midBox ibox239),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox239 113 (FixedTape.rowsAux denominator ibox239 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox239) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_239
private noncomputable def tree238 : TapeTree := .centered (candidateRows ibox238) (candidateRows (FixedTape.midBox ibox238))
attribute [irreducible] tree238
private theorem sign_238 : 2*denominator*(computed denominator (FixedTape.midBox ibox238)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox238).gradient k).lo.natAbs ((computed denominator ibox238).gradient k).hi.natAbs : Int)*((ibox238 k).hi-(ibox238 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox238
    (computed denominator ibox238) (computed denominator (FixedTape.midBox ibox238))
    (by decide +kernel)
private theorem midpoint_even_238 : ∀ k, 2 ∣ (ibox238 k).lo+(ibox238 k).hi := by decide +kernel
private theorem accepted_238 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox238) tree238 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox238 midpoint_even_238
  simp only [tree238,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox238,candidate_valid h (FixedTape.midBox ibox238),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox238 113 (FixedTape.rowsAux denominator ibox238 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox238) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_238
private noncomputable def tree237 : TapeTree := .face 2 false (candidateRows ibox237) tree238
attribute [irreducible] tree237
private theorem sign_237 : ((computed denominator ibox237).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_237 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox237) tree237 = true := by
  simp only [tree237,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox237,?_,accepted_238 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox237)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox237).gradient 2).hi) denominator_positive).1 sign_237
private noncomputable def tree236 : TapeTree := .split 2 (((1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree237 tree239
attribute [irreducible] tree236
private theorem accepted_236 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox236) tree236 = true := by
  simp only [tree236,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox236 2 (1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 : Int) false,decode_split denominator ibox236 2 (1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_237 h,accepted_239 h⟩
private noncomputable def tree235 : TapeTree := .split 1 (((1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree236 tree240
attribute [irreducible] tree235
private theorem accepted_235 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox235) tree235 = true := by
  simp only [tree235,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox235 1 (1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 : Int) false,decode_split denominator ibox235 1 (1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_236 h,accepted_240 h⟩
private noncomputable def tree234 : TapeTree := .centered (candidateRows ibox234) (candidateRows (FixedTape.midBox ibox234))
attribute [irreducible] tree234
private theorem sign_234 : 2*denominator*(computed denominator (FixedTape.midBox ibox234)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox234).gradient k).lo.natAbs ((computed denominator ibox234).gradient k).hi.natAbs : Int)*((ibox234 k).hi-(ibox234 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox234
    (computed denominator ibox234) (computed denominator (FixedTape.midBox ibox234))
    (by decide +kernel)
private theorem midpoint_even_234 : ∀ k, 2 ∣ (ibox234 k).lo+(ibox234 k).hi := by decide +kernel
private theorem accepted_234 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox234) tree234 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox234 midpoint_even_234
  simp only [tree234,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox234,candidate_valid h (FixedTape.midBox ibox234),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox234 113 (FixedTape.rowsAux denominator ibox234 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox234) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_234
private noncomputable def tree233 : TapeTree := .face 2 false (candidateRows ibox233) tree234
attribute [irreducible] tree233
private theorem sign_233 : ((computed denominator ibox233).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_233 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox233) tree233 = true := by
  simp only [tree233,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox233,?_,accepted_234 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox233)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox233).gradient 2).hi) denominator_positive).1 sign_233
private noncomputable def tree232 : TapeTree := .centered (candidateRows ibox232) (candidateRows (FixedTape.midBox ibox232))
attribute [irreducible] tree232
private theorem sign_232 : 2*denominator*(computed denominator (FixedTape.midBox ibox232)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox232).gradient k).lo.natAbs ((computed denominator ibox232).gradient k).hi.natAbs : Int)*((ibox232 k).hi-(ibox232 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox232
    (computed denominator ibox232) (computed denominator (FixedTape.midBox ibox232))
    (by decide +kernel)
private theorem midpoint_even_232 : ∀ k, 2 ∣ (ibox232 k).lo+(ibox232 k).hi := by decide +kernel
private theorem accepted_232 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox232) tree232 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox232 midpoint_even_232
  simp only [tree232,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox232,candidate_valid h (FixedTape.midBox ibox232),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox232 113 (FixedTape.rowsAux denominator ibox232 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox232) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_232
private noncomputable def tree231 : TapeTree := .face 2 false (candidateRows ibox231) tree232
attribute [irreducible] tree231
private theorem sign_231 : ((computed denominator ibox231).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_231 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox231) tree231 = true := by
  simp only [tree231,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox231,?_,accepted_232 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox231)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox231).gradient 2).hi) denominator_positive).1 sign_231
private noncomputable def tree230 : TapeTree := .split 2 (((1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree231 tree233
attribute [irreducible] tree230
private theorem accepted_230 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox230) tree230 = true := by
  simp only [tree230,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox230 2 (1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 : Int) false,decode_split denominator ibox230 2 (1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_231 h,accepted_233 h⟩
private noncomputable def tree229 : TapeTree := .centered (candidateRows ibox229) (candidateRows (FixedTape.midBox ibox229))
attribute [irreducible] tree229
private theorem sign_229 : 2*denominator*(computed denominator (FixedTape.midBox ibox229)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox229).gradient k).lo.natAbs ((computed denominator ibox229).gradient k).hi.natAbs : Int)*((ibox229 k).hi-(ibox229 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox229
    (computed denominator ibox229) (computed denominator (FixedTape.midBox ibox229))
    (by decide +kernel)
private theorem midpoint_even_229 : ∀ k, 2 ∣ (ibox229 k).lo+(ibox229 k).hi := by decide +kernel
private theorem accepted_229 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox229) tree229 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox229 midpoint_even_229
  simp only [tree229,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox229,candidate_valid h (FixedTape.midBox ibox229),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox229 113 (FixedTape.rowsAux denominator ibox229 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox229) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_229
private noncomputable def tree228 : TapeTree := .centered (candidateRows ibox228) (candidateRows (FixedTape.midBox ibox228))
attribute [irreducible] tree228
private theorem sign_228 : 2*denominator*(computed denominator (FixedTape.midBox ibox228)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox228).gradient k).lo.natAbs ((computed denominator ibox228).gradient k).hi.natAbs : Int)*((ibox228 k).hi-(ibox228 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox228
    (computed denominator ibox228) (computed denominator (FixedTape.midBox ibox228))
    (by decide +kernel)
private theorem midpoint_even_228 : ∀ k, 2 ∣ (ibox228 k).lo+(ibox228 k).hi := by decide +kernel
private theorem accepted_228 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox228) tree228 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox228 midpoint_even_228
  simp only [tree228,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox228,candidate_valid h (FixedTape.midBox ibox228),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox228 113 (FixedTape.rowsAux denominator ibox228 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox228) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_228
private noncomputable def tree227 : TapeTree := .centered (candidateRows ibox227) (candidateRows (FixedTape.midBox ibox227))
attribute [irreducible] tree227
private theorem sign_227 : 2*denominator*(computed denominator (FixedTape.midBox ibox227)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox227).gradient k).lo.natAbs ((computed denominator ibox227).gradient k).hi.natAbs : Int)*((ibox227 k).hi-(ibox227 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox227
    (computed denominator ibox227) (computed denominator (FixedTape.midBox ibox227))
    (by decide +kernel)
private theorem midpoint_even_227 : ∀ k, 2 ∣ (ibox227 k).lo+(ibox227 k).hi := by decide +kernel
private theorem accepted_227 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox227) tree227 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox227 midpoint_even_227
  simp only [tree227,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox227,candidate_valid h (FixedTape.midBox ibox227),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox227 113 (FixedTape.rowsAux denominator ibox227 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox227) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_227
private noncomputable def tree226 : TapeTree := .split 2 (((1597856087374868866056380113655380090351566177506278932563874671493120000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree227 tree228
attribute [irreducible] tree226
private theorem accepted_226 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox226) tree226 = true := by
  simp only [tree226,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox226 2 (1597856087374868866056380113655380090351566177506278932563874671493120000000000000000000000000 : Int) false,decode_split denominator ibox226 2 (1597856087374868866056380113655380090351566177506278932563874671493120000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_227 h,accepted_228 h⟩
private noncomputable def tree225 : TapeTree := .split 2 (((1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree226 tree229
attribute [irreducible] tree225
private theorem accepted_225 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox225) tree225 = true := by
  simp only [tree225,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox225 2 (1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 : Int) false,decode_split denominator ibox225 2 (1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_226 h,accepted_229 h⟩
private noncomputable def tree224 : TapeTree := .split 1 (((1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree225 tree230
attribute [irreducible] tree224
private theorem accepted_224 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox224) tree224 = true := by
  simp only [tree224,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox224 1 (1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) false,decode_split denominator ibox224 1 (1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_225 h,accepted_230 h⟩
private noncomputable def tree223 : TapeTree := .centered (candidateRows ibox223) (candidateRows (FixedTape.midBox ibox223))
attribute [irreducible] tree223
private theorem sign_223 : 2*denominator*(computed denominator (FixedTape.midBox ibox223)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox223).gradient k).lo.natAbs ((computed denominator ibox223).gradient k).hi.natAbs : Int)*((ibox223 k).hi-(ibox223 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox223
    (computed denominator ibox223) (computed denominator (FixedTape.midBox ibox223))
    (by decide +kernel)
private theorem midpoint_even_223 : ∀ k, 2 ∣ (ibox223 k).lo+(ibox223 k).hi := by decide +kernel
private theorem accepted_223 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox223) tree223 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox223 midpoint_even_223
  simp only [tree223,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox223,candidate_valid h (FixedTape.midBox ibox223),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox223 113 (FixedTape.rowsAux denominator ibox223 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox223) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_223
private noncomputable def tree222 : TapeTree := .centered (candidateRows ibox222) (candidateRows (FixedTape.midBox ibox222))
attribute [irreducible] tree222
private theorem sign_222 : 2*denominator*(computed denominator (FixedTape.midBox ibox222)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox222).gradient k).lo.natAbs ((computed denominator ibox222).gradient k).hi.natAbs : Int)*((ibox222 k).hi-(ibox222 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox222
    (computed denominator ibox222) (computed denominator (FixedTape.midBox ibox222))
    (by decide +kernel)
private theorem midpoint_even_222 : ∀ k, 2 ∣ (ibox222 k).lo+(ibox222 k).hi := by decide +kernel
private theorem accepted_222 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox222) tree222 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox222 midpoint_even_222
  simp only [tree222,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox222,candidate_valid h (FixedTape.midBox ibox222),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox222 113 (FixedTape.rowsAux denominator ibox222 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox222) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_222
private noncomputable def tree221 : TapeTree := .split 2 (((1725684574364858375340890522747810497579691471706781247168984645212569600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree222 tree223
attribute [irreducible] tree221
private theorem accepted_221 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox221) tree221 = true := by
  simp only [tree221,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox221 2 (1725684574364858375340890522747810497579691471706781247168984645212569600000000000000000000000 : Int) false,decode_split denominator ibox221 2 (1725684574364858375340890522747810497579691471706781247168984645212569600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_222 h,accepted_223 h⟩
private noncomputable def tree220 : TapeTree := .centered (candidateRows ibox220) (candidateRows (FixedTape.midBox ibox220))
attribute [irreducible] tree220
private theorem sign_220 : 2*denominator*(computed denominator (FixedTape.midBox ibox220)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox220).gradient k).lo.natAbs ((computed denominator ibox220).gradient k).hi.natAbs : Int)*((ibox220 k).hi-(ibox220 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox220
    (computed denominator ibox220) (computed denominator (FixedTape.midBox ibox220))
    (by decide +kernel)
private theorem midpoint_even_220 : ∀ k, 2 ∣ (ibox220 k).lo+(ibox220 k).hi := by decide +kernel
private theorem accepted_220 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox220) tree220 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox220 midpoint_even_220
  simp only [tree220,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox220,candidate_valid h (FixedTape.midBox ibox220),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox220 113 (FixedTape.rowsAux denominator ibox220 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox220) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_220
private noncomputable def tree219 : TapeTree := .centered (candidateRows ibox219) (candidateRows (FixedTape.midBox ibox219))
attribute [irreducible] tree219
private theorem sign_219 : 2*denominator*(computed denominator (FixedTape.midBox ibox219)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox219).gradient k).lo.natAbs ((computed denominator ibox219).gradient k).hi.natAbs : Int)*((ibox219 k).hi-(ibox219 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox219
    (computed denominator ibox219) (computed denominator (FixedTape.midBox ibox219))
    (by decide +kernel)
private theorem midpoint_even_219 : ∀ k, 2 ∣ (ibox219 k).lo+(ibox219 k).hi := by decide +kernel
private theorem accepted_219 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox219) tree219 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox219 midpoint_even_219
  simp only [tree219,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox219,candidate_valid h (FixedTape.midBox ibox219),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox219 113 (FixedTape.rowsAux denominator ibox219 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox219) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_219
private noncomputable def tree218 : TapeTree := .split 2 (((1597856087374868866056380113655380090351566177506278932563874671493120000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree219 tree220
attribute [irreducible] tree218
private theorem accepted_218 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox218) tree218 = true := by
  simp only [tree218,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox218 2 (1597856087374868866056380113655380090351566177506278932563874671493120000000000000000000000000 : Int) false,decode_split denominator ibox218 2 (1597856087374868866056380113655380090351566177506278932563874671493120000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_219 h,accepted_220 h⟩
private noncomputable def tree217 : TapeTree := .centered (candidateRows ibox217) (candidateRows (FixedTape.midBox ibox217))
attribute [irreducible] tree217
private theorem sign_217 : 2*denominator*(computed denominator (FixedTape.midBox ibox217)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox217).gradient k).lo.natAbs ((computed denominator ibox217).gradient k).hi.natAbs : Int)*((ibox217 k).hi-(ibox217 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox217
    (computed denominator ibox217) (computed denominator (FixedTape.midBox ibox217))
    (by decide +kernel)
private theorem midpoint_even_217 : ∀ k, 2 ∣ (ibox217 k).lo+(ibox217 k).hi := by decide +kernel
private theorem accepted_217 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox217) tree217 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox217 midpoint_even_217
  simp only [tree217,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox217,candidate_valid h (FixedTape.midBox ibox217),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox217 113 (FixedTape.rowsAux denominator ibox217 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox217) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_217
private noncomputable def tree216 : TapeTree := .centered (candidateRows ibox216) (candidateRows (FixedTape.midBox ibox216))
attribute [irreducible] tree216
private theorem sign_216 : 2*denominator*(computed denominator (FixedTape.midBox ibox216)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox216).gradient k).lo.natAbs ((computed denominator ibox216).gradient k).hi.natAbs : Int)*((ibox216 k).hi-(ibox216 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox216
    (computed denominator ibox216) (computed denominator (FixedTape.midBox ibox216))
    (by decide +kernel)
private theorem midpoint_even_216 : ∀ k, 2 ∣ (ibox216 k).lo+(ibox216 k).hi := by decide +kernel
private theorem accepted_216 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox216) tree216 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox216 midpoint_even_216
  simp only [tree216,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox216,candidate_valid h (FixedTape.midBox ibox216),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox216 113 (FixedTape.rowsAux denominator ibox216 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox216) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_216
private noncomputable def tree215 : TapeTree := .split 2 (((1597856087374868866056380113655380090351566177506278932563874671493120000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree216 tree217
attribute [irreducible] tree215
private theorem accepted_215 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox215) tree215 = true := by
  simp only [tree215,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox215 2 (1597856087374868866056380113655380090351566177506278932563874671493120000000000000000000000000 : Int) false,decode_split denominator ibox215 2 (1597856087374868866056380113655380090351566177506278932563874671493120000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_216 h,accepted_217 h⟩
private noncomputable def tree214 : TapeTree := .split 1 (((511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree215 tree218
attribute [irreducible] tree214
private theorem accepted_214 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox214) tree214 = true := by
  simp only [tree214,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox214 1 (511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) false,decode_split denominator ibox214 1 (511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_215 h,accepted_218 h⟩
private noncomputable def tree213 : TapeTree := .split 2 (((1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree214 tree221
attribute [irreducible] tree213
private theorem accepted_213 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox213) tree213 = true := by
  simp only [tree213,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox213 2 (1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 : Int) false,decode_split denominator ibox213 2 (1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_214 h,accepted_221 h⟩
private noncomputable def tree212 : TapeTree := .split 1 (((1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree213 tree224
attribute [irreducible] tree212
private theorem accepted_212 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox212) tree212 = true := by
  simp only [tree212,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox212 1 (1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 : Int) false,decode_split denominator ibox212 1 (1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_213 h,accepted_224 h⟩
private noncomputable def tree211 : TapeTree := .split 2 (((1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree212 tree235
attribute [irreducible] tree211
private theorem accepted_211 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox211) tree211 = true := by
  simp only [tree211,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox211 2 (1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) false,decode_split denominator ibox211 2 (1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_212 h,accepted_235 h⟩
private noncomputable def tree210 : TapeTree := .centered (candidateRows ibox210) (candidateRows (FixedTape.midBox ibox210))
attribute [irreducible] tree210
private theorem sign_210 : 2*denominator*(computed denominator (FixedTape.midBox ibox210)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox210).gradient k).lo.natAbs ((computed denominator ibox210).gradient k).hi.natAbs : Int)*((ibox210 k).hi-(ibox210 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox210
    (computed denominator ibox210) (computed denominator (FixedTape.midBox ibox210))
    (by decide +kernel)
private theorem midpoint_even_210 : ∀ k, 2 ∣ (ibox210 k).lo+(ibox210 k).hi := by decide +kernel
private theorem accepted_210 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox210) tree210 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox210 midpoint_even_210
  simp only [tree210,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox210,candidate_valid h (FixedTape.midBox ibox210),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox210 113 (FixedTape.rowsAux denominator ibox210 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox210) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_210
private noncomputable def tree209 : TapeTree := .centered (candidateRows ibox209) (candidateRows (FixedTape.midBox ibox209))
attribute [irreducible] tree209
private theorem sign_209 : 2*denominator*(computed denominator (FixedTape.midBox ibox209)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox209).gradient k).lo.natAbs ((computed denominator ibox209).gradient k).hi.natAbs : Int)*((ibox209 k).hi-(ibox209 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox209
    (computed denominator ibox209) (computed denominator (FixedTape.midBox ibox209))
    (by decide +kernel)
private theorem midpoint_even_209 : ∀ k, 2 ∣ (ibox209 k).lo+(ibox209 k).hi := by decide +kernel
private theorem accepted_209 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox209) tree209 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox209 midpoint_even_209
  simp only [tree209,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox209,candidate_valid h (FixedTape.midBox ibox209),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox209 113 (FixedTape.rowsAux denominator ibox209 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox209) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_209
private noncomputable def tree208 : TapeTree := .split 1 (((1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree209 tree210
attribute [irreducible] tree208
private theorem accepted_208 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox208) tree208 = true := by
  simp only [tree208,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox208 1 (1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) false,decode_split denominator ibox208 1 (1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_209 h,accepted_210 h⟩
private noncomputable def tree207 : TapeTree := .centered (candidateRows ibox207) (candidateRows (FixedTape.midBox ibox207))
attribute [irreducible] tree207
private theorem sign_207 : 2*denominator*(computed denominator (FixedTape.midBox ibox207)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox207).gradient k).lo.natAbs ((computed denominator ibox207).gradient k).hi.natAbs : Int)*((ibox207 k).hi-(ibox207 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox207
    (computed denominator ibox207) (computed denominator (FixedTape.midBox ibox207))
    (by decide +kernel)
private theorem midpoint_even_207 : ∀ k, 2 ∣ (ibox207 k).lo+(ibox207 k).hi := by decide +kernel
private theorem accepted_207 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox207) tree207 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox207 midpoint_even_207
  simp only [tree207,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox207,candidate_valid h (FixedTape.midBox ibox207),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox207 113 (FixedTape.rowsAux denominator ibox207 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox207) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_207
private noncomputable def tree206 : TapeTree := .centered (candidateRows ibox206) (candidateRows (FixedTape.midBox ibox206))
attribute [irreducible] tree206
private theorem sign_206 : 2*denominator*(computed denominator (FixedTape.midBox ibox206)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox206).gradient k).lo.natAbs ((computed denominator ibox206).gradient k).hi.natAbs : Int)*((ibox206 k).hi-(ibox206 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox206
    (computed denominator ibox206) (computed denominator (FixedTape.midBox ibox206))
    (by decide +kernel)
private theorem midpoint_even_206 : ∀ k, 2 ∣ (ibox206 k).lo+(ibox206 k).hi := by decide +kernel
private theorem accepted_206 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox206) tree206 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox206 midpoint_even_206
  simp only [tree206,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox206,candidate_valid h (FixedTape.midBox ibox206),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox206 113 (FixedTape.rowsAux denominator ibox206 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox206) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_206
private noncomputable def tree205 : TapeTree := .split 1 (((1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree206 tree207
attribute [irreducible] tree205
private theorem accepted_205 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox205) tree205 = true := by
  simp only [tree205,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox205 1 (1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) false,decode_split denominator ibox205 1 (1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_206 h,accepted_207 h⟩
private noncomputable def tree204 : TapeTree := .split 2 (((1406113356889884602129614500016734479509378236205525460656209710913945600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree205 tree208
attribute [irreducible] tree204
private theorem accepted_204 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox204) tree204 = true := by
  simp only [tree204,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox204 2 (1406113356889884602129614500016734479509378236205525460656209710913945600000000000000000000000 : Int) false,decode_split denominator ibox204 2 (1406113356889884602129614500016734479509378236205525460656209710913945600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_205 h,accepted_208 h⟩
private noncomputable def tree203 : TapeTree := .centered (candidateRows ibox203) (candidateRows (FixedTape.midBox ibox203))
attribute [irreducible] tree203
private theorem sign_203 : 2*denominator*(computed denominator (FixedTape.midBox ibox203)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox203).gradient k).lo.natAbs ((computed denominator ibox203).gradient k).hi.natAbs : Int)*((ibox203 k).hi-(ibox203 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox203
    (computed denominator ibox203) (computed denominator (FixedTape.midBox ibox203))
    (by decide +kernel)
private theorem midpoint_even_203 : ∀ k, 2 ∣ (ibox203 k).lo+(ibox203 k).hi := by decide +kernel
private theorem accepted_203 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox203) tree203 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox203 midpoint_even_203
  simp only [tree203,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox203,candidate_valid h (FixedTape.midBox ibox203),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox203 113 (FixedTape.rowsAux denominator ibox203 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox203) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_203
private noncomputable def tree202 : TapeTree := .centered (candidateRows ibox202) (candidateRows (FixedTape.midBox ibox202))
attribute [irreducible] tree202
private theorem sign_202 : 2*denominator*(computed denominator (FixedTape.midBox ibox202)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox202).gradient k).lo.natAbs ((computed denominator ibox202).gradient k).hi.natAbs : Int)*((ibox202 k).hi-(ibox202 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox202
    (computed denominator ibox202) (computed denominator (FixedTape.midBox ibox202))
    (by decide +kernel)
private theorem midpoint_even_202 : ∀ k, 2 ∣ (ibox202 k).lo+(ibox202 k).hi := by decide +kernel
private theorem accepted_202 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox202) tree202 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox202 midpoint_even_202
  simp only [tree202,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox202,candidate_valid h (FixedTape.midBox ibox202),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox202 113 (FixedTape.rowsAux denominator ibox202 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox202) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_202
private noncomputable def tree201 : TapeTree := .split 2 (((1470027600384879356771869704562949683123440883305776617958764697773670400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree202 tree203
attribute [irreducible] tree201
private theorem accepted_201 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox201) tree201 = true := by
  simp only [tree201,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox201 2 (1470027600384879356771869704562949683123440883305776617958764697773670400000000000000000000000 : Int) false,decode_split denominator ibox201 2 (1470027600384879356771869704562949683123440883305776617958764697773670400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_202 h,accepted_203 h⟩
private noncomputable def tree200 : TapeTree := .centered (candidateRows ibox200) (candidateRows (FixedTape.midBox ibox200))
attribute [irreducible] tree200
private theorem sign_200 : 2*denominator*(computed denominator (FixedTape.midBox ibox200)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox200).gradient k).lo.natAbs ((computed denominator ibox200).gradient k).hi.natAbs : Int)*((ibox200 k).hi-(ibox200 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox200
    (computed denominator ibox200) (computed denominator (FixedTape.midBox ibox200))
    (by decide +kernel)
private theorem midpoint_even_200 : ∀ k, 2 ∣ (ibox200 k).lo+(ibox200 k).hi := by decide +kernel
private theorem accepted_200 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox200) tree200 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox200 midpoint_even_200
  simp only [tree200,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox200,candidate_valid h (FixedTape.midBox ibox200),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox200 113 (FixedTape.rowsAux denominator ibox200 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox200) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_200
private noncomputable def tree199 : TapeTree := .centered (candidateRows ibox199) (candidateRows (FixedTape.midBox ibox199))
attribute [irreducible] tree199
private theorem sign_199 : 2*denominator*(computed denominator (FixedTape.midBox ibox199)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox199).gradient k).lo.natAbs ((computed denominator ibox199).gradient k).hi.natAbs : Int)*((ibox199 k).hi-(ibox199 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox199
    (computed denominator ibox199) (computed denominator (FixedTape.midBox ibox199))
    (by decide +kernel)
private theorem midpoint_even_199 : ∀ k, 2 ∣ (ibox199 k).lo+(ibox199 k).hi := by decide +kernel
private theorem accepted_199 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox199) tree199 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox199 midpoint_even_199
  simp only [tree199,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox199,candidate_valid h (FixedTape.midBox ibox199),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox199 113 (FixedTape.rowsAux denominator ibox199 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox199) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_199
private noncomputable def tree198 : TapeTree := .split 1 (((1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree199 tree200
attribute [irreducible] tree198
private theorem accepted_198 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox198) tree198 = true := by
  simp only [tree198,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox198 1 (1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) false,decode_split denominator ibox198 1 (1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_199 h,accepted_200 h⟩
private noncomputable def tree197 : TapeTree := .split 2 (((1406113356889884602129614500016734479509378236205525460656209710913945600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree198 tree201
attribute [irreducible] tree197
private theorem accepted_197 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox197) tree197 = true := by
  simp only [tree197,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox197 2 (1406113356889884602129614500016734479509378236205525460656209710913945600000000000000000000000 : Int) false,decode_split denominator ibox197 2 (1406113356889884602129614500016734479509378236205525460656209710913945600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_198 h,accepted_201 h⟩
private noncomputable def tree196 : TapeTree := .split 1 (((1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree197 tree204
attribute [irreducible] tree196
private theorem accepted_196 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox196) tree196 = true := by
  simp only [tree196,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox196 1 (1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) false,decode_split denominator ibox196 1 (1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_197 h,accepted_204 h⟩
private noncomputable def tree195 : TapeTree := .centered (candidateRows ibox195) (candidateRows (FixedTape.midBox ibox195))
attribute [irreducible] tree195
private theorem sign_195 : 2*denominator*(computed denominator (FixedTape.midBox ibox195)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox195).gradient k).lo.natAbs ((computed denominator ibox195).gradient k).hi.natAbs : Int)*((ibox195 k).hi-(ibox195 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox195
    (computed denominator ibox195) (computed denominator (FixedTape.midBox ibox195))
    (by decide +kernel)
private theorem midpoint_even_195 : ∀ k, 2 ∣ (ibox195 k).lo+(ibox195 k).hi := by decide +kernel
private theorem accepted_195 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox195) tree195 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox195 midpoint_even_195
  simp only [tree195,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox195,candidate_valid h (FixedTape.midBox ibox195),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox195 113 (FixedTape.rowsAux denominator ibox195 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox195) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_195
private noncomputable def tree194 : TapeTree := .centered (candidateRows ibox194) (candidateRows (FixedTape.midBox ibox194))
attribute [irreducible] tree194
private theorem sign_194 : 2*denominator*(computed denominator (FixedTape.midBox ibox194)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox194).gradient k).lo.natAbs ((computed denominator ibox194).gradient k).hi.natAbs : Int)*((ibox194 k).hi-(ibox194 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox194
    (computed denominator ibox194) (computed denominator (FixedTape.midBox ibox194))
    (by decide +kernel)
private theorem midpoint_even_194 : ∀ k, 2 ∣ (ibox194 k).lo+(ibox194 k).hi := by decide +kernel
private theorem accepted_194 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox194) tree194 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox194 midpoint_even_194
  simp only [tree194,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox194,candidate_valid h (FixedTape.midBox ibox194),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox194 113 (FixedTape.rowsAux denominator ibox194 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox194) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_194
private noncomputable def tree193 : TapeTree := .split 1 (((1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree194 tree195
attribute [irreducible] tree193
private theorem accepted_193 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox193) tree193 = true := by
  simp only [tree193,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox193 1 (1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) false,decode_split denominator ibox193 1 (1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_194 h,accepted_195 h⟩
private noncomputable def tree192 : TapeTree := .centered (candidateRows ibox192) (candidateRows (FixedTape.midBox ibox192))
attribute [irreducible] tree192
private theorem sign_192 : 2*denominator*(computed denominator (FixedTape.midBox ibox192)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox192).gradient k).lo.natAbs ((computed denominator ibox192).gradient k).hi.natAbs : Int)*((ibox192 k).hi-(ibox192 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox192
    (computed denominator ibox192) (computed denominator (FixedTape.midBox ibox192))
    (by decide +kernel)
private theorem midpoint_even_192 : ∀ k, 2 ∣ (ibox192 k).lo+(ibox192 k).hi := by decide +kernel
private theorem accepted_192 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox192) tree192 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox192 midpoint_even_192
  simp only [tree192,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox192,candidate_valid h (FixedTape.midBox ibox192),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox192 113 (FixedTape.rowsAux denominator ibox192 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox192) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_192
private noncomputable def tree191 : TapeTree := .centered (candidateRows ibox191) (candidateRows (FixedTape.midBox ibox191))
attribute [irreducible] tree191
private theorem sign_191 : 2*denominator*(computed denominator (FixedTape.midBox ibox191)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox191).gradient k).lo.natAbs ((computed denominator ibox191).gradient k).hi.natAbs : Int)*((ibox191 k).hi-(ibox191 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox191
    (computed denominator ibox191) (computed denominator (FixedTape.midBox ibox191))
    (by decide +kernel)
private theorem midpoint_even_191 : ∀ k, 2 ∣ (ibox191 k).lo+(ibox191 k).hi := by decide +kernel
private theorem accepted_191 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox191) tree191 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox191 midpoint_even_191
  simp only [tree191,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox191,candidate_valid h (FixedTape.midBox ibox191),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox191 113 (FixedTape.rowsAux denominator ibox191 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox191) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_191
private noncomputable def tree190 : TapeTree := .split 2 (((1086542139414910828918338477285658461439065000704269674143434776615321600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree191 tree192
attribute [irreducible] tree190
private theorem accepted_190 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox190) tree190 = true := by
  simp only [tree190,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox190 2 (1086542139414910828918338477285658461439065000704269674143434776615321600000000000000000000000 : Int) false,decode_split denominator ibox190 2 (1086542139414910828918338477285658461439065000704269674143434776615321600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_191 h,accepted_192 h⟩
private noncomputable def tree189 : TapeTree := .centered (candidateRows ibox189) (candidateRows (FixedTape.midBox ibox189))
attribute [irreducible] tree189
private theorem sign_189 : 2*denominator*(computed denominator (FixedTape.midBox ibox189)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox189).gradient k).lo.natAbs ((computed denominator ibox189).gradient k).hi.natAbs : Int)*((ibox189 k).hi-(ibox189 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox189
    (computed denominator ibox189) (computed denominator (FixedTape.midBox ibox189))
    (by decide +kernel)
private theorem midpoint_even_189 : ∀ k, 2 ∣ (ibox189 k).lo+(ibox189 k).hi := by decide +kernel
private theorem accepted_189 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox189) tree189 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox189 midpoint_even_189
  simp only [tree189,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox189,candidate_valid h (FixedTape.midBox ibox189),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox189 113 (FixedTape.rowsAux denominator ibox189 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox189) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_189
private noncomputable def tree188 : TapeTree := .split 1 (((1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree189 tree190
attribute [irreducible] tree188
private theorem accepted_188 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox188) tree188 = true := by
  simp only [tree188,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox188 1 (1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) false,decode_split denominator ibox188 1 (1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_189 h,accepted_190 h⟩
private noncomputable def tree187 : TapeTree := .split 2 (((1150456382909905583560593681831873665053127647804520831445989763475046400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree188 tree193
attribute [irreducible] tree187
private theorem accepted_187 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox187) tree187 = true := by
  simp only [tree187,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox187 2 (1150456382909905583560593681831873665053127647804520831445989763475046400000000000000000000000 : Int) false,decode_split denominator ibox187 2 (1150456382909905583560593681831873665053127647804520831445989763475046400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_188 h,accepted_193 h⟩
private noncomputable def tree186 : TapeTree := .centered (candidateRows ibox186) (candidateRows (FixedTape.midBox ibox186))
attribute [irreducible] tree186
private theorem sign_186 : 2*denominator*(computed denominator (FixedTape.midBox ibox186)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox186).gradient k).lo.natAbs ((computed denominator ibox186).gradient k).hi.natAbs : Int)*((ibox186 k).hi-(ibox186 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox186
    (computed denominator ibox186) (computed denominator (FixedTape.midBox ibox186))
    (by decide +kernel)
private theorem midpoint_even_186 : ∀ k, 2 ∣ (ibox186 k).lo+(ibox186 k).hi := by decide +kernel
private theorem accepted_186 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox186) tree186 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox186 midpoint_even_186
  simp only [tree186,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox186,candidate_valid h (FixedTape.midBox ibox186),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox186 113 (FixedTape.rowsAux denominator ibox186 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox186) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_186
private noncomputable def tree185 : TapeTree := .centered (candidateRows ibox185) (candidateRows (FixedTape.midBox ibox185))
attribute [irreducible] tree185
private theorem sign_185 : 2*denominator*(computed denominator (FixedTape.midBox ibox185)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox185).gradient k).lo.natAbs ((computed denominator ibox185).gradient k).hi.natAbs : Int)*((ibox185 k).hi-(ibox185 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox185
    (computed denominator ibox185) (computed denominator (FixedTape.midBox ibox185))
    (by decide +kernel)
private theorem midpoint_even_185 : ∀ k, 2 ∣ (ibox185 k).lo+(ibox185 k).hi := by decide +kernel
private theorem accepted_185 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox185) tree185 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox185 midpoint_even_185
  simp only [tree185,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox185,candidate_valid h (FixedTape.midBox ibox185),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox185 113 (FixedTape.rowsAux denominator ibox185 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox185) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_185
private noncomputable def tree184 : TapeTree := .split 1 (((1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree185 tree186
attribute [irreducible] tree184
private theorem accepted_184 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox184) tree184 = true := by
  simp only [tree184,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox184 1 (1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) false,decode_split denominator ibox184 1 (1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_185 h,accepted_186 h⟩
private noncomputable def tree183 : TapeTree := .centered (candidateRows ibox183) (candidateRows (FixedTape.midBox ibox183))
attribute [irreducible] tree183
private theorem sign_183 : 2*denominator*(computed denominator (FixedTape.midBox ibox183)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox183).gradient k).lo.natAbs ((computed denominator ibox183).gradient k).hi.natAbs : Int)*((ibox183 k).hi-(ibox183 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox183
    (computed denominator ibox183) (computed denominator (FixedTape.midBox ibox183))
    (by decide +kernel)
private theorem midpoint_even_183 : ∀ k, 2 ∣ (ibox183 k).lo+(ibox183 k).hi := by decide +kernel
private theorem accepted_183 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox183) tree183 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox183 midpoint_even_183
  simp only [tree183,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox183,candidate_valid h (FixedTape.midBox ibox183),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox183 113 (FixedTape.rowsAux denominator ibox183 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox183) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_183
private noncomputable def tree182 : TapeTree := .centered (candidateRows ibox182) (candidateRows (FixedTape.midBox ibox182))
attribute [irreducible] tree182
private theorem sign_182 : 2*denominator*(computed denominator (FixedTape.midBox ibox182)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox182).gradient k).lo.natAbs ((computed denominator ibox182).gradient k).hi.natAbs : Int)*((ibox182 k).hi-(ibox182 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox182
    (computed denominator ibox182) (computed denominator (FixedTape.midBox ibox182))
    (by decide +kernel)
private theorem midpoint_even_182 : ∀ k, 2 ∣ (ibox182 k).lo+(ibox182 k).hi := by decide +kernel
private theorem accepted_182 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox182) tree182 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox182 midpoint_even_182
  simp only [tree182,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox182,candidate_valid h (FixedTape.midBox ibox182),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox182 113 (FixedTape.rowsAux denominator ibox182 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox182) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_182
private noncomputable def tree181 : TapeTree := .split 1 (((1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree182 tree183
attribute [irreducible] tree181
private theorem accepted_181 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox181) tree181 = true := by
  simp only [tree181,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox181 1 (1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) false,decode_split denominator ibox181 1 (1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_182 h,accepted_183 h⟩
private noncomputable def tree180 : TapeTree := .split 2 (((1150456382909905583560593681831873665053127647804520831445989763475046400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree181 tree184
attribute [irreducible] tree180
private theorem accepted_180 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox180) tree180 = true := by
  simp only [tree180,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox180 2 (1150456382909905583560593681831873665053127647804520831445989763475046400000000000000000000000 : Int) false,decode_split denominator ibox180 2 (1150456382909905583560593681831873665053127647804520831445989763475046400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_181 h,accepted_184 h⟩
private noncomputable def tree179 : TapeTree := .split 1 (((1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree180 tree187
attribute [irreducible] tree179
private theorem accepted_179 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox179) tree179 = true := by
  simp only [tree179,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox179 1 (1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) false,decode_split denominator ibox179 1 (1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_180 h,accepted_187 h⟩
private noncomputable def tree178 : TapeTree := .split 2 (((1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree179 tree196
attribute [irreducible] tree178
private theorem accepted_178 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox178) tree178 = true := by
  simp only [tree178,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox178 2 (1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) false,decode_split denominator ibox178 2 (1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_179 h,accepted_196 h⟩
private noncomputable def tree177 : TapeTree := .centered (candidateRows ibox177) (candidateRows (FixedTape.midBox ibox177))
attribute [irreducible] tree177
private theorem sign_177 : 2*denominator*(computed denominator (FixedTape.midBox ibox177)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox177).gradient k).lo.natAbs ((computed denominator ibox177).gradient k).hi.natAbs : Int)*((ibox177 k).hi-(ibox177 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox177
    (computed denominator ibox177) (computed denominator (FixedTape.midBox ibox177))
    (by decide +kernel)
private theorem midpoint_even_177 : ∀ k, 2 ∣ (ibox177 k).lo+(ibox177 k).hi := by decide +kernel
private theorem accepted_177 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox177) tree177 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox177 midpoint_even_177
  simp only [tree177,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox177,candidate_valid h (FixedTape.midBox ibox177),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox177 113 (FixedTape.rowsAux denominator ibox177 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox177) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_177
private noncomputable def tree176 : TapeTree := .centered (candidateRows ibox176) (candidateRows (FixedTape.midBox ibox176))
attribute [irreducible] tree176
private theorem sign_176 : 2*denominator*(computed denominator (FixedTape.midBox ibox176)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox176).gradient k).lo.natAbs ((computed denominator ibox176).gradient k).hi.natAbs : Int)*((ibox176 k).hi-(ibox176 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox176
    (computed denominator ibox176) (computed denominator (FixedTape.midBox ibox176))
    (by decide +kernel)
private theorem midpoint_even_176 : ∀ k, 2 ∣ (ibox176 k).lo+(ibox176 k).hi := by decide +kernel
private theorem accepted_176 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox176) tree176 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox176 midpoint_even_176
  simp only [tree176,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox176,candidate_valid h (FixedTape.midBox ibox176),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox176 113 (FixedTape.rowsAux denominator ibox176 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox176) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_176
private noncomputable def tree175 : TapeTree := .split 2 (((1470027600384879356771869704562949683123440883305776617958764697773670400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree176 tree177
attribute [irreducible] tree175
private theorem accepted_175 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox175) tree175 = true := by
  simp only [tree175,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox175 2 (1470027600384879356771869704562949683123440883305776617958764697773670400000000000000000000000 : Int) false,decode_split denominator ibox175 2 (1470027600384879356771869704562949683123440883305776617958764697773670400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_176 h,accepted_177 h⟩
private noncomputable def tree174 : TapeTree := .centered (candidateRows ibox174) (candidateRows (FixedTape.midBox ibox174))
attribute [irreducible] tree174
private theorem sign_174 : 2*denominator*(computed denominator (FixedTape.midBox ibox174)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox174).gradient k).lo.natAbs ((computed denominator ibox174).gradient k).hi.natAbs : Int)*((ibox174 k).hi-(ibox174 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox174
    (computed denominator ibox174) (computed denominator (FixedTape.midBox ibox174))
    (by decide +kernel)
private theorem midpoint_even_174 : ∀ k, 2 ∣ (ibox174 k).lo+(ibox174 k).hi := by decide +kernel
private theorem accepted_174 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox174) tree174 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox174 midpoint_even_174
  simp only [tree174,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox174,candidate_valid h (FixedTape.midBox ibox174),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox174 113 (FixedTape.rowsAux denominator ibox174 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox174) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_174
private noncomputable def tree173 : TapeTree := .centered (candidateRows ibox173) (candidateRows (FixedTape.midBox ibox173))
attribute [irreducible] tree173
private theorem sign_173 : 2*denominator*(computed denominator (FixedTape.midBox ibox173)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox173).gradient k).lo.natAbs ((computed denominator ibox173).gradient k).hi.natAbs : Int)*((ibox173 k).hi-(ibox173 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox173
    (computed denominator ibox173) (computed denominator (FixedTape.midBox ibox173))
    (by decide +kernel)
private theorem midpoint_even_173 : ∀ k, 2 ∣ (ibox173 k).lo+(ibox173 k).hi := by decide +kernel
private theorem accepted_173 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox173) tree173 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox173 midpoint_even_173
  simp only [tree173,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox173,candidate_valid h (FixedTape.midBox ibox173),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox173 113 (FixedTape.rowsAux denominator ibox173 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox173) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_173
private noncomputable def tree172 : TapeTree := .split 2 (((1470027600384879356771869704562949683123440883305776617958764697773670400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree173 tree174
attribute [irreducible] tree172
private theorem accepted_172 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox172) tree172 = true := by
  simp only [tree172,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox172 2 (1470027600384879356771869704562949683123440883305776617958764697773670400000000000000000000000 : Int) false,decode_split denominator ibox172 2 (1470027600384879356771869704562949683123440883305776617958764697773670400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_173 h,accepted_174 h⟩
private noncomputable def tree171 : TapeTree := .split 1 (((511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree172 tree175
attribute [irreducible] tree171
private theorem accepted_171 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox171) tree171 = true := by
  simp only [tree171,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox171 1 (511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) false,decode_split denominator ibox171 1 (511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_172 h,accepted_175 h⟩
private noncomputable def tree170 : TapeTree := .centered (candidateRows ibox170) (candidateRows (FixedTape.midBox ibox170))
attribute [irreducible] tree170
private theorem sign_170 : 2*denominator*(computed denominator (FixedTape.midBox ibox170)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox170).gradient k).lo.natAbs ((computed denominator ibox170).gradient k).hi.natAbs : Int)*((ibox170 k).hi-(ibox170 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox170
    (computed denominator ibox170) (computed denominator (FixedTape.midBox ibox170))
    (by decide +kernel)
private theorem midpoint_even_170 : ∀ k, 2 ∣ (ibox170 k).lo+(ibox170 k).hi := by decide +kernel
private theorem accepted_170 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox170) tree170 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox170 midpoint_even_170
  simp only [tree170,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox170,candidate_valid h (FixedTape.midBox ibox170),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox170 113 (FixedTape.rowsAux denominator ibox170 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox170) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_170
private noncomputable def tree169 : TapeTree := .centered (candidateRows ibox169) (candidateRows (FixedTape.midBox ibox169))
attribute [irreducible] tree169
private theorem sign_169 : 2*denominator*(computed denominator (FixedTape.midBox ibox169)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox169).gradient k).lo.natAbs ((computed denominator ibox169).gradient k).hi.natAbs : Int)*((ibox169 k).hi-(ibox169 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox169
    (computed denominator ibox169) (computed denominator (FixedTape.midBox ibox169))
    (by decide +kernel)
private theorem midpoint_even_169 : ∀ k, 2 ∣ (ibox169 k).lo+(ibox169 k).hi := by decide +kernel
private theorem accepted_169 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox169) tree169 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox169 midpoint_even_169
  simp only [tree169,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox169,candidate_valid h (FixedTape.midBox ibox169),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox169 113 (FixedTape.rowsAux denominator ibox169 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox169) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_169
private noncomputable def tree168 : TapeTree := .split 1 (((766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree169 tree170
attribute [irreducible] tree168
private theorem accepted_168 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox168) tree168 = true := by
  simp only [tree168,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox168 1 (766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) false,decode_split denominator ibox168 1 (766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_169 h,accepted_170 h⟩
private noncomputable def tree167 : TapeTree := .centered (candidateRows ibox167) (candidateRows (FixedTape.midBox ibox167))
attribute [irreducible] tree167
private theorem sign_167 : 2*denominator*(computed denominator (FixedTape.midBox ibox167)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox167).gradient k).lo.natAbs ((computed denominator ibox167).gradient k).hi.natAbs : Int)*((ibox167 k).hi-(ibox167 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox167
    (computed denominator ibox167) (computed denominator (FixedTape.midBox ibox167))
    (by decide +kernel)
private theorem midpoint_even_167 : ∀ k, 2 ∣ (ibox167 k).lo+(ibox167 k).hi := by decide +kernel
private theorem accepted_167 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox167) tree167 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox167 midpoint_even_167
  simp only [tree167,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox167,candidate_valid h (FixedTape.midBox ibox167),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox167 113 (FixedTape.rowsAux denominator ibox167 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox167) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_167
private noncomputable def tree166 : TapeTree := .centered (candidateRows ibox166) (candidateRows (FixedTape.midBox ibox166))
attribute [irreducible] tree166
private theorem sign_166 : 2*denominator*(computed denominator (FixedTape.midBox ibox166)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox166).gradient k).lo.natAbs ((computed denominator ibox166).gradient k).hi.natAbs : Int)*((ibox166 k).hi-(ibox166 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox166
    (computed denominator ibox166) (computed denominator (FixedTape.midBox ibox166))
    (by decide +kernel)
private theorem midpoint_even_166 : ∀ k, 2 ∣ (ibox166 k).lo+(ibox166 k).hi := by decide +kernel
private theorem accepted_166 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox166) tree166 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox166 midpoint_even_166
  simp only [tree166,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox166,candidate_valid h (FixedTape.midBox ibox166),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox166 113 (FixedTape.rowsAux denominator ibox166 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox166) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_166
private noncomputable def tree165 : TapeTree := .split 1 (((255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree166 tree167
attribute [irreducible] tree165
private theorem accepted_165 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox165) tree165 = true := by
  simp only [tree165,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox165 1 (255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) false,decode_split denominator ibox165 1 (255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_166 h,accepted_167 h⟩
private noncomputable def tree164 : TapeTree := .split 1 (((511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree165 tree168
attribute [irreducible] tree164
private theorem accepted_164 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox164) tree164 = true := by
  simp only [tree164,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox164 1 (511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) false,decode_split denominator ibox164 1 (511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_165 h,accepted_168 h⟩
private noncomputable def tree163 : TapeTree := .split 2 (((1406113356889884602129614500016734479509378236205525460656209710913945600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree164 tree171
attribute [irreducible] tree163
private theorem accepted_163 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox163) tree163 = true := by
  simp only [tree163,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox163 2 (1406113356889884602129614500016734479509378236205525460656209710913945600000000000000000000000 : Int) false,decode_split denominator ibox163 2 (1406113356889884602129614500016734479509378236205525460656209710913945600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_164 h,accepted_171 h⟩
private noncomputable def tree162 : TapeTree := .centered (candidateRows ibox162) (candidateRows (FixedTape.midBox ibox162))
attribute [irreducible] tree162
private theorem sign_162 : 2*denominator*(computed denominator (FixedTape.midBox ibox162)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox162).gradient k).lo.natAbs ((computed denominator ibox162).gradient k).hi.natAbs : Int)*((ibox162 k).hi-(ibox162 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox162
    (computed denominator ibox162) (computed denominator (FixedTape.midBox ibox162))
    (by decide +kernel)
private theorem midpoint_even_162 : ∀ k, 2 ∣ (ibox162 k).lo+(ibox162 k).hi := by decide +kernel
private theorem accepted_162 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox162) tree162 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox162 midpoint_even_162
  simp only [tree162,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox162,candidate_valid h (FixedTape.midBox ibox162),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox162 113 (FixedTape.rowsAux denominator ibox162 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox162) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_162
private noncomputable def tree161 : TapeTree := .centered (candidateRows ibox161) (candidateRows (FixedTape.midBox ibox161))
attribute [irreducible] tree161
private theorem sign_161 : 2*denominator*(computed denominator (FixedTape.midBox ibox161)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox161).gradient k).lo.natAbs ((computed denominator ibox161).gradient k).hi.natAbs : Int)*((ibox161 k).hi-(ibox161 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox161
    (computed denominator ibox161) (computed denominator (FixedTape.midBox ibox161))
    (by decide +kernel)
private theorem midpoint_even_161 : ∀ k, 2 ∣ (ibox161 k).lo+(ibox161 k).hi := by decide +kernel
private theorem accepted_161 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox161) tree161 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox161 midpoint_even_161
  simp only [tree161,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox161,candidate_valid h (FixedTape.midBox ibox161),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox161 113 (FixedTape.rowsAux denominator ibox161 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox161) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_161
private noncomputable def tree160 : TapeTree := .split 1 (((766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree161 tree162
attribute [irreducible] tree160
private theorem accepted_160 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox160) tree160 = true := by
  simp only [tree160,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox160 1 (766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) false,decode_split denominator ibox160 1 (766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_161 h,accepted_162 h⟩
private noncomputable def tree159 : TapeTree := .centered (candidateRows ibox159) (candidateRows (FixedTape.midBox ibox159))
attribute [irreducible] tree159
private theorem sign_159 : 2*denominator*(computed denominator (FixedTape.midBox ibox159)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox159).gradient k).lo.natAbs ((computed denominator ibox159).gradient k).hi.natAbs : Int)*((ibox159 k).hi-(ibox159 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox159
    (computed denominator ibox159) (computed denominator (FixedTape.midBox ibox159))
    (by decide +kernel)
private theorem midpoint_even_159 : ∀ k, 2 ∣ (ibox159 k).lo+(ibox159 k).hi := by decide +kernel
private theorem accepted_159 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox159) tree159 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox159 midpoint_even_159
  simp only [tree159,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox159,candidate_valid h (FixedTape.midBox ibox159),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox159 113 (FixedTape.rowsAux denominator ibox159 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox159) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_159
private noncomputable def tree158 : TapeTree := .split 2 (((1150456382909905583560593681831873665053127647804520831445989763475046400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree159 tree160
attribute [irreducible] tree158
private theorem accepted_158 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox158) tree158 = true := by
  simp only [tree158,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox158 2 (1150456382909905583560593681831873665053127647804520831445989763475046400000000000000000000000 : Int) false,decode_split denominator ibox158 2 (1150456382909905583560593681831873665053127647804520831445989763475046400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_159 h,accepted_160 h⟩
private noncomputable def tree157 : TapeTree := .centered (candidateRows ibox157) (candidateRows (FixedTape.midBox ibox157))
attribute [irreducible] tree157
private theorem sign_157 : 2*denominator*(computed denominator (FixedTape.midBox ibox157)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox157).gradient k).lo.natAbs ((computed denominator ibox157).gradient k).hi.natAbs : Int)*((ibox157 k).hi-(ibox157 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox157
    (computed denominator ibox157) (computed denominator (FixedTape.midBox ibox157))
    (by decide +kernel)
private theorem midpoint_even_157 : ∀ k, 2 ∣ (ibox157 k).lo+(ibox157 k).hi := by decide +kernel
private theorem accepted_157 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox157) tree157 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox157 midpoint_even_157
  simp only [tree157,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox157,candidate_valid h (FixedTape.midBox ibox157),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox157 113 (FixedTape.rowsAux denominator ibox157 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox157) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_157
private noncomputable def tree156 : TapeTree := .centered (candidateRows ibox156) (candidateRows (FixedTape.midBox ibox156))
attribute [irreducible] tree156
private theorem sign_156 : 2*denominator*(computed denominator (FixedTape.midBox ibox156)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox156).gradient k).lo.natAbs ((computed denominator ibox156).gradient k).hi.natAbs : Int)*((ibox156 k).hi-(ibox156 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox156
    (computed denominator ibox156) (computed denominator (FixedTape.midBox ibox156))
    (by decide +kernel)
private theorem midpoint_even_156 : ∀ k, 2 ∣ (ibox156 k).lo+(ibox156 k).hi := by decide +kernel
private theorem accepted_156 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox156) tree156 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox156 midpoint_even_156
  simp only [tree156,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox156,candidate_valid h (FixedTape.midBox ibox156),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox156 113 (FixedTape.rowsAux denominator ibox156 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox156) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_156
private noncomputable def tree155 : TapeTree := .split 2 (((1150456382909905583560593681831873665053127647804520831445989763475046400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree156 tree157
attribute [irreducible] tree155
private theorem accepted_155 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox155) tree155 = true := by
  simp only [tree155,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox155 2 (1150456382909905583560593681831873665053127647804520831445989763475046400000000000000000000000 : Int) false,decode_split denominator ibox155 2 (1150456382909905583560593681831873665053127647804520831445989763475046400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_156 h,accepted_157 h⟩
private noncomputable def tree154 : TapeTree := .split 1 (((511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree155 tree158
attribute [irreducible] tree154
private theorem accepted_154 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox154) tree154 = true := by
  simp only [tree154,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox154 1 (511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) false,decode_split denominator ibox154 1 (511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_155 h,accepted_158 h⟩
private noncomputable def tree153 : TapeTree := .split 2 (((1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree154 tree163
attribute [irreducible] tree153
private theorem accepted_153 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox153) tree153 = true := by
  simp only [tree153,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox153 2 (1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) false,decode_split denominator ibox153 2 (1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_154 h,accepted_163 h⟩
private noncomputable def tree152 : TapeTree := .split 1 (((1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree153 tree178
attribute [irreducible] tree152
private theorem accepted_152 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox152) tree152 = true := by
  simp only [tree152,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox152 1 (1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 : Int) false,decode_split denominator ibox152 1 (1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_153 h,accepted_178 h⟩
private noncomputable def tree151 : TapeTree := .split 2 (((1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree152 tree211
attribute [irreducible] tree151
private theorem accepted_151 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox151) tree151 = true := by
  simp only [tree151,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox151 2 (1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) false,decode_split denominator ibox151 2 (1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_152 h,accepted_211 h⟩
private noncomputable def tree150 : TapeTree := .centered (candidateRows ibox150) (candidateRows (FixedTape.midBox ibox150))
attribute [irreducible] tree150
private theorem sign_150 : 2*denominator*(computed denominator (FixedTape.midBox ibox150)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox150).gradient k).lo.natAbs ((computed denominator ibox150).gradient k).hi.natAbs : Int)*((ibox150 k).hi-(ibox150 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox150
    (computed denominator ibox150) (computed denominator (FixedTape.midBox ibox150))
    (by decide +kernel)
private theorem midpoint_even_150 : ∀ k, 2 ∣ (ibox150 k).lo+(ibox150 k).hi := by decide +kernel
private theorem accepted_150 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox150) tree150 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox150 midpoint_even_150
  simp only [tree150,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox150,candidate_valid h (FixedTape.midBox ibox150),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox150 113 (FixedTape.rowsAux denominator ibox150 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox150) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_150
private noncomputable def tree149 : TapeTree := .centered (candidateRows ibox149) (candidateRows (FixedTape.midBox ibox149))
attribute [irreducible] tree149
private theorem sign_149 : 2*denominator*(computed denominator (FixedTape.midBox ibox149)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox149).gradient k).lo.natAbs ((computed denominator ibox149).gradient k).hi.natAbs : Int)*((ibox149 k).hi-(ibox149 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox149
    (computed denominator ibox149) (computed denominator (FixedTape.midBox ibox149))
    (by decide +kernel)
private theorem midpoint_even_149 : ∀ k, 2 ∣ (ibox149 k).lo+(ibox149 k).hi := by decide +kernel
private theorem accepted_149 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox149) tree149 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox149 midpoint_even_149
  simp only [tree149,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox149,candidate_valid h (FixedTape.midBox ibox149),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox149 113 (FixedTape.rowsAux denominator ibox149 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox149) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_149
private noncomputable def tree148 : TapeTree := .split 0 (((1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree149 tree150
attribute [irreducible] tree148
private theorem accepted_148 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox148) tree148 = true := by
  simp only [tree148,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox148 0 (1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) false,decode_split denominator ibox148 0 (1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_149 h,accepted_150 h⟩
private noncomputable def tree147 : TapeTree := .centered (candidateRows ibox147) (candidateRows (FixedTape.midBox ibox147))
attribute [irreducible] tree147
private theorem sign_147 : 2*denominator*(computed denominator (FixedTape.midBox ibox147)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox147).gradient k).lo.natAbs ((computed denominator ibox147).gradient k).hi.natAbs : Int)*((ibox147 k).hi-(ibox147 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox147
    (computed denominator ibox147) (computed denominator (FixedTape.midBox ibox147))
    (by decide +kernel)
private theorem midpoint_even_147 : ∀ k, 2 ∣ (ibox147 k).lo+(ibox147 k).hi := by decide +kernel
private theorem accepted_147 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox147) tree147 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox147 midpoint_even_147
  simp only [tree147,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox147,candidate_valid h (FixedTape.midBox ibox147),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox147 113 (FixedTape.rowsAux denominator ibox147 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox147) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_147
private noncomputable def tree146 : TapeTree := .centered (candidateRows ibox146) (candidateRows (FixedTape.midBox ibox146))
attribute [irreducible] tree146
private theorem sign_146 : 2*denominator*(computed denominator (FixedTape.midBox ibox146)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox146).gradient k).lo.natAbs ((computed denominator ibox146).gradient k).hi.natAbs : Int)*((ibox146 k).hi-(ibox146 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox146
    (computed denominator ibox146) (computed denominator (FixedTape.midBox ibox146))
    (by decide +kernel)
private theorem midpoint_even_146 : ∀ k, 2 ∣ (ibox146 k).lo+(ibox146 k).hi := by decide +kernel
private theorem accepted_146 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox146) tree146 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox146 midpoint_even_146
  simp only [tree146,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox146,candidate_valid h (FixedTape.midBox ibox146),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox146 113 (FixedTape.rowsAux denominator ibox146 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox146) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_146
private noncomputable def tree145 : TapeTree := .split 2 (((830885165434931810349317659100797646982814412303265044933214829176422400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree146 tree147
attribute [irreducible] tree145
private theorem accepted_145 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox145) tree145 = true := by
  simp only [tree145,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox145 2 (830885165434931810349317659100797646982814412303265044933214829176422400000000000000000000000 : Int) false,decode_split denominator ibox145 2 (830885165434931810349317659100797646982814412303265044933214829176422400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_146 h,accepted_147 h⟩
private noncomputable def tree144 : TapeTree := .centered (candidateRows ibox144) (candidateRows (FixedTape.midBox ibox144))
attribute [irreducible] tree144
private theorem sign_144 : 2*denominator*(computed denominator (FixedTape.midBox ibox144)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox144).gradient k).lo.natAbs ((computed denominator ibox144).gradient k).hi.natAbs : Int)*((ibox144 k).hi-(ibox144 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox144
    (computed denominator ibox144) (computed denominator (FixedTape.midBox ibox144))
    (by decide +kernel)
private theorem midpoint_even_144 : ∀ k, 2 ∣ (ibox144 k).lo+(ibox144 k).hi := by decide +kernel
private theorem accepted_144 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox144) tree144 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox144 midpoint_even_144
  simp only [tree144,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox144,candidate_valid h (FixedTape.midBox ibox144),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox144 113 (FixedTape.rowsAux denominator ibox144 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox144) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_144
private noncomputable def tree143 : TapeTree := .split 1 (((1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree144 tree145
attribute [irreducible] tree143
private theorem accepted_143 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox143) tree143 = true := by
  simp only [tree143,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox143 1 (1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 : Int) false,decode_split denominator ibox143 1 (1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_144 h,accepted_145 h⟩
private noncomputable def tree142 : TapeTree := .split 2 (((894799408929926564991572863647012850596877059403516202235769816036147200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree143 tree148
attribute [irreducible] tree142
private theorem accepted_142 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox142) tree142 = true := by
  simp only [tree142,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox142 2 (894799408929926564991572863647012850596877059403516202235769816036147200000000000000000000000 : Int) false,decode_split denominator ibox142 2 (894799408929926564991572863647012850596877059403516202235769816036147200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_143 h,accepted_148 h⟩
private noncomputable def tree141 : TapeTree := .centered (candidateRows ibox141) (candidateRows (FixedTape.midBox ibox141))
attribute [irreducible] tree141
private theorem sign_141 : 2*denominator*(computed denominator (FixedTape.midBox ibox141)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox141).gradient k).lo.natAbs ((computed denominator ibox141).gradient k).hi.natAbs : Int)*((ibox141 k).hi-(ibox141 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox141
    (computed denominator ibox141) (computed denominator (FixedTape.midBox ibox141))
    (by decide +kernel)
private theorem midpoint_even_141 : ∀ k, 2 ∣ (ibox141 k).lo+(ibox141 k).hi := by decide +kernel
private theorem accepted_141 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox141) tree141 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox141 midpoint_even_141
  simp only [tree141,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox141,candidate_valid h (FixedTape.midBox ibox141),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox141 113 (FixedTape.rowsAux denominator ibox141 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox141) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_141
private noncomputable def tree140 : TapeTree := .centered (candidateRows ibox140) (candidateRows (FixedTape.midBox ibox140))
attribute [irreducible] tree140
private theorem sign_140 : 2*denominator*(computed denominator (FixedTape.midBox ibox140)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox140).gradient k).lo.natAbs ((computed denominator ibox140).gradient k).hi.natAbs : Int)*((ibox140 k).hi-(ibox140 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox140
    (computed denominator ibox140) (computed denominator (FixedTape.midBox ibox140))
    (by decide +kernel)
private theorem midpoint_even_140 : ∀ k, 2 ∣ (ibox140 k).lo+(ibox140 k).hi := by decide +kernel
private theorem accepted_140 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox140) tree140 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox140 midpoint_even_140
  simp only [tree140,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox140,candidate_valid h (FixedTape.midBox ibox140),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox140 113 (FixedTape.rowsAux denominator ibox140 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox140) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_140
private noncomputable def tree139 : TapeTree := .split 2 (((894799408929926564991572863647012850596877059403516202235769816036147200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree140 tree141
attribute [irreducible] tree139
private theorem accepted_139 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox139) tree139 = true := by
  simp only [tree139,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox139 2 (894799408929926564991572863647012850596877059403516202235769816036147200000000000000000000000 : Int) false,decode_split denominator ibox139 2 (894799408929926564991572863647012850596877059403516202235769816036147200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_140 h,accepted_141 h⟩
private noncomputable def tree138 : TapeTree := .split 1 (((1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree139 tree142
attribute [irreducible] tree138
private theorem accepted_138 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox138) tree138 = true := by
  simp only [tree138,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox138 1 (1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) false,decode_split denominator ibox138 1 (1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_139 h,accepted_142 h⟩
private noncomputable def tree137 : TapeTree := .centered (candidateRows ibox137) (candidateRows (FixedTape.midBox ibox137))
attribute [irreducible] tree137
private theorem sign_137 : 2*denominator*(computed denominator (FixedTape.midBox ibox137)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox137).gradient k).lo.natAbs ((computed denominator ibox137).gradient k).hi.natAbs : Int)*((ibox137 k).hi-(ibox137 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox137
    (computed denominator ibox137) (computed denominator (FixedTape.midBox ibox137))
    (by decide +kernel)
private theorem midpoint_even_137 : ∀ k, 2 ∣ (ibox137 k).lo+(ibox137 k).hi := by decide +kernel
private theorem accepted_137 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox137) tree137 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox137 midpoint_even_137
  simp only [tree137,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox137,candidate_valid h (FixedTape.midBox ibox137),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox137 113 (FixedTape.rowsAux denominator ibox137 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox137) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_137
private noncomputable def tree136 : TapeTree := .centered (candidateRows ibox136) (candidateRows (FixedTape.midBox ibox136))
attribute [irreducible] tree136
private theorem sign_136 : 2*denominator*(computed denominator (FixedTape.midBox ibox136)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox136).gradient k).lo.natAbs ((computed denominator ibox136).gradient k).hi.natAbs : Int)*((ibox136 k).hi-(ibox136 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox136
    (computed denominator ibox136) (computed denominator (FixedTape.midBox ibox136))
    (by decide +kernel)
private theorem midpoint_even_136 : ∀ k, 2 ∣ (ibox136 k).lo+(ibox136 k).hi := by decide +kernel
private theorem accepted_136 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox136) tree136 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox136 midpoint_even_136
  simp only [tree136,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox136,candidate_valid h (FixedTape.midBox ibox136),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox136 113 (FixedTape.rowsAux denominator ibox136 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox136) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_136
private noncomputable def tree135 : TapeTree := .split 0 (((1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree136 tree137
attribute [irreducible] tree135
private theorem accepted_135 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox135) tree135 = true := by
  simp only [tree135,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox135 0 (1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) false,decode_split denominator ibox135 0 (1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_136 h,accepted_137 h⟩
private noncomputable def tree134 : TapeTree := .centered (candidateRows ibox134) (candidateRows (FixedTape.midBox ibox134))
attribute [irreducible] tree134
private theorem sign_134 : 2*denominator*(computed denominator (FixedTape.midBox ibox134)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox134).gradient k).lo.natAbs ((computed denominator ibox134).gradient k).hi.natAbs : Int)*((ibox134 k).hi-(ibox134 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox134
    (computed denominator ibox134) (computed denominator (FixedTape.midBox ibox134))
    (by decide +kernel)
private theorem midpoint_even_134 : ∀ k, 2 ∣ (ibox134 k).lo+(ibox134 k).hi := by decide +kernel
private theorem accepted_134 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox134) tree134 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox134 midpoint_even_134
  simp only [tree134,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox134,candidate_valid h (FixedTape.midBox ibox134),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox134 113 (FixedTape.rowsAux denominator ibox134 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox134) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_134
private noncomputable def tree133 : TapeTree := .split 1 (((1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree134 tree135
attribute [irreducible] tree133
private theorem accepted_133 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox133) tree133 = true := by
  simp only [tree133,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox133 1 (1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 : Int) false,decode_split denominator ibox133 1 (1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_134 h,accepted_135 h⟩
private noncomputable def tree132 : TapeTree := .centered (candidateRows ibox132) (candidateRows (FixedTape.midBox ibox132))
attribute [irreducible] tree132
private theorem sign_132 : 2*denominator*(computed denominator (FixedTape.midBox ibox132)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox132).gradient k).lo.natAbs ((computed denominator ibox132).gradient k).hi.natAbs : Int)*((ibox132 k).hi-(ibox132 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox132
    (computed denominator ibox132) (computed denominator (FixedTape.midBox ibox132))
    (by decide +kernel)
private theorem midpoint_even_132 : ∀ k, 2 ∣ (ibox132 k).lo+(ibox132 k).hi := by decide +kernel
private theorem accepted_132 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox132) tree132 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox132 midpoint_even_132
  simp only [tree132,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox132,candidate_valid h (FixedTape.midBox ibox132),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox132 113 (FixedTape.rowsAux denominator ibox132 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox132) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_132
private noncomputable def tree131 : TapeTree := .centered (candidateRows ibox131) (candidateRows (FixedTape.midBox ibox131))
attribute [irreducible] tree131
private theorem sign_131 : 2*denominator*(computed denominator (FixedTape.midBox ibox131)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox131).gradient k).lo.natAbs ((computed denominator ibox131).gradient k).hi.natAbs : Int)*((ibox131 k).hi-(ibox131 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox131
    (computed denominator ibox131) (computed denominator (FixedTape.midBox ibox131))
    (by decide +kernel)
private theorem midpoint_even_131 : ∀ k, 2 ∣ (ibox131 k).lo+(ibox131 k).hi := by decide +kernel
private theorem accepted_131 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox131) tree131 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox131 midpoint_even_131
  simp only [tree131,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox131,candidate_valid h (FixedTape.midBox ibox131),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox131 113 (FixedTape.rowsAux denominator ibox131 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox131) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_131
private noncomputable def tree130 : TapeTree := .split 0 (((1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree131 tree132
attribute [irreducible] tree130
private theorem accepted_130 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox130) tree130 = true := by
  simp only [tree130,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox130 0 (1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) false,decode_split denominator ibox130 0 (1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_131 h,accepted_132 h⟩
private noncomputable def tree129 : TapeTree := .centered (candidateRows ibox129) (candidateRows (FixedTape.midBox ibox129))
attribute [irreducible] tree129
private theorem sign_129 : 2*denominator*(computed denominator (FixedTape.midBox ibox129)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox129).gradient k).lo.natAbs ((computed denominator ibox129).gradient k).hi.natAbs : Int)*((ibox129 k).hi-(ibox129 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox129
    (computed denominator ibox129) (computed denominator (FixedTape.midBox ibox129))
    (by decide +kernel)
private theorem midpoint_even_129 : ∀ k, 2 ∣ (ibox129 k).lo+(ibox129 k).hi := by decide +kernel
private theorem accepted_129 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox129) tree129 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox129 midpoint_even_129
  simp only [tree129,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox129,candidate_valid h (FixedTape.midBox ibox129),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox129 113 (FixedTape.rowsAux denominator ibox129 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox129) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_129
private noncomputable def tree128 : TapeTree := .split 1 (((1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree129 tree130
attribute [irreducible] tree128
private theorem accepted_128 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox128) tree128 = true := by
  simp only [tree128,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox128 1 (1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 : Int) false,decode_split denominator ibox128 1 (1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_129 h,accepted_130 h⟩
private noncomputable def tree127 : TapeTree := .split 2 (((639142434949947546422552045462152036140626471002511573025549868597248000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree128 tree133
attribute [irreducible] tree127
private theorem accepted_127 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox127) tree127 = true := by
  simp only [tree127,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox127 2 (639142434949947546422552045462152036140626471002511573025549868597248000000000000000000000000 : Int) false,decode_split denominator ibox127 2 (639142434949947546422552045462152036140626471002511573025549868597248000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_128 h,accepted_133 h⟩
private noncomputable def tree126 : TapeTree := .centered (candidateRows ibox126) (candidateRows (FixedTape.midBox ibox126))
attribute [irreducible] tree126
private theorem sign_126 : 2*denominator*(computed denominator (FixedTape.midBox ibox126)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox126).gradient k).lo.natAbs ((computed denominator ibox126).gradient k).hi.natAbs : Int)*((ibox126 k).hi-(ibox126 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox126
    (computed denominator ibox126) (computed denominator (FixedTape.midBox ibox126))
    (by decide +kernel)
private theorem midpoint_even_126 : ∀ k, 2 ∣ (ibox126 k).lo+(ibox126 k).hi := by decide +kernel
private theorem accepted_126 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox126) tree126 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox126 midpoint_even_126
  simp only [tree126,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox126,candidate_valid h (FixedTape.midBox ibox126),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox126 113 (FixedTape.rowsAux denominator ibox126 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox126) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_126
private noncomputable def tree125 : TapeTree := .centered (candidateRows ibox125) (candidateRows (FixedTape.midBox ibox125))
attribute [irreducible] tree125
private theorem sign_125 : 2*denominator*(computed denominator (FixedTape.midBox ibox125)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox125).gradient k).lo.natAbs ((computed denominator ibox125).gradient k).hi.natAbs : Int)*((ibox125 k).hi-(ibox125 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox125
    (computed denominator ibox125) (computed denominator (FixedTape.midBox ibox125))
    (by decide +kernel)
private theorem midpoint_even_125 : ∀ k, 2 ∣ (ibox125 k).lo+(ibox125 k).hi := by decide +kernel
private theorem accepted_125 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox125) tree125 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox125 midpoint_even_125
  simp only [tree125,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox125,candidate_valid h (FixedTape.midBox ibox125),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox125 113 (FixedTape.rowsAux denominator ibox125 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox125) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_125
private noncomputable def tree124 : TapeTree := .split 2 (((639142434949947546422552045462152036140626471002511573025549868597248000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree125 tree126
attribute [irreducible] tree124
private theorem accepted_124 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox124) tree124 = true := by
  simp only [tree124,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox124 2 (639142434949947546422552045462152036140626471002511573025549868597248000000000000000000000000 : Int) false,decode_split denominator ibox124 2 (639142434949947546422552045462152036140626471002511573025549868597248000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_125 h,accepted_126 h⟩
private noncomputable def tree123 : TapeTree := .centered (candidateRows ibox123) (candidateRows (FixedTape.midBox ibox123))
attribute [irreducible] tree123
private theorem sign_123 : 2*denominator*(computed denominator (FixedTape.midBox ibox123)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox123).gradient k).lo.natAbs ((computed denominator ibox123).gradient k).hi.natAbs : Int)*((ibox123 k).hi-(ibox123 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox123
    (computed denominator ibox123) (computed denominator (FixedTape.midBox ibox123))
    (by decide +kernel)
private theorem midpoint_even_123 : ∀ k, 2 ∣ (ibox123 k).lo+(ibox123 k).hi := by decide +kernel
private theorem accepted_123 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox123) tree123 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox123 midpoint_even_123
  simp only [tree123,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox123,candidate_valid h (FixedTape.midBox ibox123),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox123 113 (FixedTape.rowsAux denominator ibox123 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox123) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_123
private noncomputable def tree122 : TapeTree := .split 1 (((1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree123 tree124
attribute [irreducible] tree122
private theorem accepted_122 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox122) tree122 = true := by
  simp only [tree122,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox122 1 (1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 : Int) false,decode_split denominator ibox122 1 (1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_123 h,accepted_124 h⟩
private noncomputable def tree121 : TapeTree := .split 1 (((1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree122 tree127
attribute [irreducible] tree121
private theorem accepted_121 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox121) tree121 = true := by
  simp only [tree121,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox121 1 (1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) false,decode_split denominator ibox121 1 (1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_122 h,accepted_127 h⟩
private noncomputable def tree120 : TapeTree := .split 2 (((766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree121 tree138
attribute [irreducible] tree120
private theorem accepted_120 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox120) tree120 = true := by
  simp only [tree120,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox120 2 (766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) false,decode_split denominator ibox120 2 (766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_121 h,accepted_138 h⟩
private noncomputable def tree119 : TapeTree := .centered (candidateRows ibox119) (candidateRows (FixedTape.midBox ibox119))
attribute [irreducible] tree119
private theorem sign_119 : 2*denominator*(computed denominator (FixedTape.midBox ibox119)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox119).gradient k).lo.natAbs ((computed denominator ibox119).gradient k).hi.natAbs : Int)*((ibox119 k).hi-(ibox119 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox119
    (computed denominator ibox119) (computed denominator (FixedTape.midBox ibox119))
    (by decide +kernel)
private theorem midpoint_even_119 : ∀ k, 2 ∣ (ibox119 k).lo+(ibox119 k).hi := by decide +kernel
private theorem accepted_119 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox119) tree119 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox119 midpoint_even_119
  simp only [tree119,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox119,candidate_valid h (FixedTape.midBox ibox119),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox119 113 (FixedTape.rowsAux denominator ibox119 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox119) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_119
private noncomputable def tree118 : TapeTree := .centered (candidateRows ibox118) (candidateRows (FixedTape.midBox ibox118))
attribute [irreducible] tree118
private theorem sign_118 : 2*denominator*(computed denominator (FixedTape.midBox ibox118)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox118).gradient k).lo.natAbs ((computed denominator ibox118).gradient k).hi.natAbs : Int)*((ibox118 k).hi-(ibox118 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox118
    (computed denominator ibox118) (computed denominator (FixedTape.midBox ibox118))
    (by decide +kernel)
private theorem midpoint_even_118 : ∀ k, 2 ∣ (ibox118 k).lo+(ibox118 k).hi := by decide +kernel
private theorem accepted_118 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox118) tree118 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox118 midpoint_even_118
  simp only [tree118,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox118,candidate_valid h (FixedTape.midBox ibox118),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox118 113 (FixedTape.rowsAux denominator ibox118 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox118) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_118
private noncomputable def tree117 : TapeTree := .split 2 (((894799408929926564991572863647012850596877059403516202235769816036147200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree118 tree119
attribute [irreducible] tree117
private theorem accepted_117 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox117) tree117 = true := by
  simp only [tree117,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox117 2 (894799408929926564991572863647012850596877059403516202235769816036147200000000000000000000000 : Int) false,decode_split denominator ibox117 2 (894799408929926564991572863647012850596877059403516202235769816036147200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_118 h,accepted_119 h⟩
private noncomputable def tree116 : TapeTree := .centered (candidateRows ibox116) (candidateRows (FixedTape.midBox ibox116))
attribute [irreducible] tree116
private theorem sign_116 : 2*denominator*(computed denominator (FixedTape.midBox ibox116)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox116).gradient k).lo.natAbs ((computed denominator ibox116).gradient k).hi.natAbs : Int)*((ibox116 k).hi-(ibox116 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox116
    (computed denominator ibox116) (computed denominator (FixedTape.midBox ibox116))
    (by decide +kernel)
private theorem midpoint_even_116 : ∀ k, 2 ∣ (ibox116 k).lo+(ibox116 k).hi := by decide +kernel
private theorem accepted_116 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox116) tree116 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox116 midpoint_even_116
  simp only [tree116,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox116,candidate_valid h (FixedTape.midBox ibox116),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox116 113 (FixedTape.rowsAux denominator ibox116 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox116) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_116
private noncomputable def tree115 : TapeTree := .split 1 (((1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree116 tree117
attribute [irreducible] tree115
private theorem accepted_115 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox115) tree115 = true := by
  simp only [tree115,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox115 1 (1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) false,decode_split denominator ibox115 1 (1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_116 h,accepted_117 h⟩
private noncomputable def tree114 : TapeTree := .centered (candidateRows ibox114) (candidateRows (FixedTape.midBox ibox114))
attribute [irreducible] tree114
private theorem sign_114 : 2*denominator*(computed denominator (FixedTape.midBox ibox114)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox114).gradient k).lo.natAbs ((computed denominator ibox114).gradient k).hi.natAbs : Int)*((ibox114 k).hi-(ibox114 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox114
    (computed denominator ibox114) (computed denominator (FixedTape.midBox ibox114))
    (by decide +kernel)
private theorem midpoint_even_114 : ∀ k, 2 ∣ (ibox114 k).lo+(ibox114 k).hi := by decide +kernel
private theorem accepted_114 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox114) tree114 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox114 midpoint_even_114
  simp only [tree114,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox114,candidate_valid h (FixedTape.midBox ibox114),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox114 113 (FixedTape.rowsAux denominator ibox114 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox114) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_114
private noncomputable def tree113 : TapeTree := .centered (candidateRows ibox113) (candidateRows (FixedTape.midBox ibox113))
attribute [irreducible] tree113
private theorem sign_113 : 2*denominator*(computed denominator (FixedTape.midBox ibox113)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox113).gradient k).lo.natAbs ((computed denominator ibox113).gradient k).hi.natAbs : Int)*((ibox113 k).hi-(ibox113 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox113
    (computed denominator ibox113) (computed denominator (FixedTape.midBox ibox113))
    (by decide +kernel)
private theorem midpoint_even_113 : ∀ k, 2 ∣ (ibox113 k).lo+(ibox113 k).hi := by decide +kernel
private theorem accepted_113 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox113) tree113 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox113 midpoint_even_113
  simp only [tree113,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox113,candidate_valid h (FixedTape.midBox ibox113),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox113 113 (FixedTape.rowsAux denominator ibox113 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox113) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_113
private noncomputable def tree112 : TapeTree := .split 1 (((1406113356889884602129614500016734479509378236205525460656209710913945600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree113 tree114
attribute [irreducible] tree112
private theorem accepted_112 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox112) tree112 = true := by
  simp only [tree112,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox112 1 (1406113356889884602129614500016734479509378236205525460656209710913945600000000000000000000000 : Int) false,decode_split denominator ibox112 1 (1406113356889884602129614500016734479509378236205525460656209710913945600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_113 h,accepted_114 h⟩
private noncomputable def tree111 : TapeTree := .centered (candidateRows ibox111) (candidateRows (FixedTape.midBox ibox111))
attribute [irreducible] tree111
private theorem sign_111 : 2*denominator*(computed denominator (FixedTape.midBox ibox111)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox111).gradient k).lo.natAbs ((computed denominator ibox111).gradient k).hi.natAbs : Int)*((ibox111 k).hi-(ibox111 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox111
    (computed denominator ibox111) (computed denominator (FixedTape.midBox ibox111))
    (by decide +kernel)
private theorem midpoint_even_111 : ∀ k, 2 ∣ (ibox111 k).lo+(ibox111 k).hi := by decide +kernel
private theorem accepted_111 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox111) tree111 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox111 midpoint_even_111
  simp only [tree111,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox111,candidate_valid h (FixedTape.midBox ibox111),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox111 113 (FixedTape.rowsAux denominator ibox111 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox111) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_111
private noncomputable def tree110 : TapeTree := .split 1 (((1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree111 tree112
attribute [irreducible] tree110
private theorem accepted_110 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox110) tree110 = true := by
  simp only [tree110,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox110 1 (1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) false,decode_split denominator ibox110 1 (1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_111 h,accepted_112 h⟩
private noncomputable def tree109 : TapeTree := .split 2 (((766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree110 tree115
attribute [irreducible] tree109
private theorem accepted_109 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox109) tree109 = true := by
  simp only [tree109,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox109 2 (766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) false,decode_split denominator ibox109 2 (766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_110 h,accepted_115 h⟩
private noncomputable def tree108 : TapeTree := .split 1 (((1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree109 tree120
attribute [irreducible] tree108
private theorem accepted_108 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox108) tree108 = true := by
  simp only [tree108,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox108 1 (1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) false,decode_split denominator ibox108 1 (1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_109 h,accepted_120 h⟩
private noncomputable def tree107 : TapeTree := .centered (candidateRows ibox107) (candidateRows (FixedTape.midBox ibox107))
attribute [irreducible] tree107
private theorem sign_107 : 2*denominator*(computed denominator (FixedTape.midBox ibox107)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox107).gradient k).lo.natAbs ((computed denominator ibox107).gradient k).hi.natAbs : Int)*((ibox107 k).hi-(ibox107 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox107
    (computed denominator ibox107) (computed denominator (FixedTape.midBox ibox107))
    (by decide +kernel)
private theorem midpoint_even_107 : ∀ k, 2 ∣ (ibox107 k).lo+(ibox107 k).hi := by decide +kernel
private theorem accepted_107 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox107) tree107 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox107 midpoint_even_107
  simp only [tree107,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox107,candidate_valid h (FixedTape.midBox ibox107),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox107 113 (FixedTape.rowsAux denominator ibox107 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox107) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_107
private noncomputable def tree106 : TapeTree := .face 1 true (candidateRows ibox106) tree107
attribute [irreducible] tree106
private theorem sign_106 : 0 ≤ ((computed denominator ibox106).gradient 1).lo := by decide +kernel
private theorem accepted_106 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox106) tree106 = true := by
  simp only [tree106,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox106,?_,accepted_107 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox106)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox106).gradient 1).lo) denominator_positive).2 sign_106
private noncomputable def tree105 : TapeTree := .centered (candidateRows ibox105) (candidateRows (FixedTape.midBox ibox105))
attribute [irreducible] tree105
private theorem sign_105 : 2*denominator*(computed denominator (FixedTape.midBox ibox105)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox105).gradient k).lo.natAbs ((computed denominator ibox105).gradient k).hi.natAbs : Int)*((ibox105 k).hi-(ibox105 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox105
    (computed denominator ibox105) (computed denominator (FixedTape.midBox ibox105))
    (by decide +kernel)
private theorem midpoint_even_105 : ∀ k, 2 ∣ (ibox105 k).lo+(ibox105 k).hi := by decide +kernel
private theorem accepted_105 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox105) tree105 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox105 midpoint_even_105
  simp only [tree105,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox105,candidate_valid h (FixedTape.midBox ibox105),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox105 113 (FixedTape.rowsAux denominator ibox105 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox105) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_105
private noncomputable def tree104 : TapeTree := .face 1 true (candidateRows ibox104) tree105
attribute [irreducible] tree104
private theorem sign_104 : 0 ≤ ((computed denominator ibox104).gradient 1).lo := by decide +kernel
private theorem accepted_104 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox104) tree104 = true := by
  simp only [tree104,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox104,?_,accepted_105 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox104)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox104).gradient 1).lo) denominator_positive).2 sign_104
private noncomputable def tree103 : TapeTree := .split 0 (((1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree104 tree106
attribute [irreducible] tree103
private theorem accepted_103 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox103) tree103 = true := by
  simp only [tree103,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox103 0 (1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) false,decode_split denominator ibox103 0 (1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_104 h,accepted_106 h⟩
private noncomputable def tree102 : TapeTree := .centered (candidateRows ibox102) (candidateRows (FixedTape.midBox ibox102))
attribute [irreducible] tree102
private theorem sign_102 : 2*denominator*(computed denominator (FixedTape.midBox ibox102)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox102).gradient k).lo.natAbs ((computed denominator ibox102).gradient k).hi.natAbs : Int)*((ibox102 k).hi-(ibox102 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox102
    (computed denominator ibox102) (computed denominator (FixedTape.midBox ibox102))
    (by decide +kernel)
private theorem midpoint_even_102 : ∀ k, 2 ∣ (ibox102 k).lo+(ibox102 k).hi := by decide +kernel
private theorem accepted_102 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox102) tree102 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox102 midpoint_even_102
  simp only [tree102,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox102,candidate_valid h (FixedTape.midBox ibox102),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox102 113 (FixedTape.rowsAux denominator ibox102 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox102) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_102
private noncomputable def tree101 : TapeTree := .centered (candidateRows ibox101) (candidateRows (FixedTape.midBox ibox101))
attribute [irreducible] tree101
private theorem sign_101 : 2*denominator*(computed denominator (FixedTape.midBox ibox101)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox101).gradient k).lo.natAbs ((computed denominator ibox101).gradient k).hi.natAbs : Int)*((ibox101 k).hi-(ibox101 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox101
    (computed denominator ibox101) (computed denominator (FixedTape.midBox ibox101))
    (by decide +kernel)
private theorem midpoint_even_101 : ∀ k, 2 ∣ (ibox101 k).lo+(ibox101 k).hi := by decide +kernel
private theorem accepted_101 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox101) tree101 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox101 midpoint_even_101
  simp only [tree101,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox101,candidate_valid h (FixedTape.midBox ibox101),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox101 113 (FixedTape.rowsAux denominator ibox101 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox101) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_101
private noncomputable def tree100 : TapeTree := .centered (candidateRows ibox100) (candidateRows (FixedTape.midBox ibox100))
attribute [irreducible] tree100
private theorem sign_100 : 2*denominator*(computed denominator (FixedTape.midBox ibox100)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox100).gradient k).lo.natAbs ((computed denominator ibox100).gradient k).hi.natAbs : Int)*((ibox100 k).hi-(ibox100 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox100
    (computed denominator ibox100) (computed denominator (FixedTape.midBox ibox100))
    (by decide +kernel)
private theorem midpoint_even_100 : ∀ k, 2 ∣ (ibox100 k).lo+(ibox100 k).hi := by decide +kernel
private theorem accepted_100 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox100) tree100 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox100 midpoint_even_100
  simp only [tree100,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox100,candidate_valid h (FixedTape.midBox ibox100),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox100 113 (FixedTape.rowsAux denominator ibox100 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox100) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_100
private noncomputable def tree99 : TapeTree := .split 0 (((1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree100 tree101
attribute [irreducible] tree99
private theorem accepted_99 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox99) tree99 = true := by
  simp only [tree99,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox99 0 (1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) false,decode_split denominator ibox99 0 (1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_100 h,accepted_101 h⟩
private noncomputable def tree98 : TapeTree := .split 2 (((319571217474973773211276022731076018070313235501255786512774934298624000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree99 tree102
attribute [irreducible] tree98
private theorem accepted_98 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox98) tree98 = true := by
  simp only [tree98,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox98 2 (319571217474973773211276022731076018070313235501255786512774934298624000000000000000000000000 : Int) false,decode_split denominator ibox98 2 (319571217474973773211276022731076018070313235501255786512774934298624000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_99 h,accepted_102 h⟩
private noncomputable def tree97 : TapeTree := .face 1 true (candidateRows ibox97) tree98
attribute [irreducible] tree97
private theorem sign_97 : 0 ≤ ((computed denominator ibox97).gradient 1).lo := by decide +kernel
private theorem accepted_97 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox97) tree97 = true := by
  simp only [tree97,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox97,?_,accepted_98 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox97)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox97).gradient 1).lo) denominator_positive).2 sign_97
private noncomputable def tree96 : TapeTree := .split 2 (((383485460969968527853531227277291221684375882601506943815329921158348800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree97 tree103
attribute [irreducible] tree96
private theorem accepted_96 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox96) tree96 = true := by
  simp only [tree96,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox96 2 (383485460969968527853531227277291221684375882601506943815329921158348800000000000000000000000 : Int) false,decode_split denominator ibox96 2 (383485460969968527853531227277291221684375882601506943815329921158348800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_97 h,accepted_103 h⟩
private noncomputable def tree95 : TapeTree := .centered (candidateRows ibox95) (candidateRows (FixedTape.midBox ibox95))
attribute [irreducible] tree95
private theorem sign_95 : 2*denominator*(computed denominator (FixedTape.midBox ibox95)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox95).gradient k).lo.natAbs ((computed denominator ibox95).gradient k).hi.natAbs : Int)*((ibox95 k).hi-(ibox95 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox95
    (computed denominator ibox95) (computed denominator (FixedTape.midBox ibox95))
    (by decide +kernel)
private theorem midpoint_even_95 : ∀ k, 2 ∣ (ibox95 k).lo+(ibox95 k).hi := by decide +kernel
private theorem accepted_95 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox95) tree95 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox95 midpoint_even_95
  simp only [tree95,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox95,candidate_valid h (FixedTape.midBox ibox95),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox95 113 (FixedTape.rowsAux denominator ibox95 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox95) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_95
private noncomputable def tree94 : TapeTree := .centered (candidateRows ibox94) (candidateRows (FixedTape.midBox ibox94))
attribute [irreducible] tree94
private theorem sign_94 : 2*denominator*(computed denominator (FixedTape.midBox ibox94)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox94).gradient k).lo.natAbs ((computed denominator ibox94).gradient k).hi.natAbs : Int)*((ibox94 k).hi-(ibox94 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox94
    (computed denominator ibox94) (computed denominator (FixedTape.midBox ibox94))
    (by decide +kernel)
private theorem midpoint_even_94 : ∀ k, 2 ∣ (ibox94 k).lo+(ibox94 k).hi := by decide +kernel
private theorem accepted_94 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox94) tree94 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox94 midpoint_even_94
  simp only [tree94,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox94,candidate_valid h (FixedTape.midBox ibox94),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox94 113 (FixedTape.rowsAux denominator ibox94 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox94) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_94
private noncomputable def tree93 : TapeTree := .split 0 (((1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree94 tree95
attribute [irreducible] tree93
private theorem accepted_93 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox93) tree93 = true := by
  simp only [tree93,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox93 0 (1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) false,decode_split denominator ibox93 0 (1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_94 h,accepted_95 h⟩
private noncomputable def tree92 : TapeTree := .centered (candidateRows ibox92) (candidateRows (FixedTape.midBox ibox92))
attribute [irreducible] tree92
private theorem sign_92 : 2*denominator*(computed denominator (FixedTape.midBox ibox92)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox92).gradient k).lo.natAbs ((computed denominator ibox92).gradient k).hi.natAbs : Int)*((ibox92 k).hi-(ibox92 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox92
    (computed denominator ibox92) (computed denominator (FixedTape.midBox ibox92))
    (by decide +kernel)
private theorem midpoint_even_92 : ∀ k, 2 ∣ (ibox92 k).lo+(ibox92 k).hi := by decide +kernel
private theorem accepted_92 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox92) tree92 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox92 midpoint_even_92
  simp only [tree92,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox92,candidate_valid h (FixedTape.midBox ibox92),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox92 113 (FixedTape.rowsAux denominator ibox92 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox92) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_92
private noncomputable def tree91 : TapeTree := .face 1 true (candidateRows ibox91) tree92
attribute [irreducible] tree91
private theorem sign_91 : 0 ≤ ((computed denominator ibox91).gradient 1).lo := by decide +kernel
private theorem accepted_91 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox91) tree91 = true := by
  simp only [tree91,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox91,?_,accepted_92 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox91)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox91).gradient 1).lo) denominator_positive).2 sign_91
private noncomputable def tree90 : TapeTree := .split 2 (((383485460969968527853531227277291221684375882601506943815329921158348800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree91 tree93
attribute [irreducible] tree90
private theorem accepted_90 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox90) tree90 = true := by
  simp only [tree90,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox90 2 (383485460969968527853531227277291221684375882601506943815329921158348800000000000000000000000 : Int) false,decode_split denominator ibox90 2 (383485460969968527853531227277291221684375882601506943815329921158348800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_91 h,accepted_93 h⟩
private noncomputable def tree89 : TapeTree := .split 1 (((1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree90 tree96
attribute [irreducible] tree89
private theorem accepted_89 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox89) tree89 = true := by
  simp only [tree89,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox89 1 (1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 : Int) false,decode_split denominator ibox89 1 (1917427304849842639267656136386456108421879413007534719076649605791744000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_90 h,accepted_96 h⟩
private noncomputable def tree88 : TapeTree := .centered (candidateRows ibox88) (candidateRows (FixedTape.midBox ibox88))
attribute [irreducible] tree88
private theorem sign_88 : 2*denominator*(computed denominator (FixedTape.midBox ibox88)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox88).gradient k).lo.natAbs ((computed denominator ibox88).gradient k).hi.natAbs : Int)*((ibox88 k).hi-(ibox88 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox88
    (computed denominator ibox88) (computed denominator (FixedTape.midBox ibox88))
    (by decide +kernel)
private theorem midpoint_even_88 : ∀ k, 2 ∣ (ibox88 k).lo+(ibox88 k).hi := by decide +kernel
private theorem accepted_88 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox88) tree88 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox88 midpoint_even_88
  simp only [tree88,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox88,candidate_valid h (FixedTape.midBox ibox88),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox88 113 (FixedTape.rowsAux denominator ibox88 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox88) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_88
private noncomputable def tree87 : TapeTree := .centered (candidateRows ibox87) (candidateRows (FixedTape.midBox ibox87))
attribute [irreducible] tree87
private theorem sign_87 : 2*denominator*(computed denominator (FixedTape.midBox ibox87)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox87).gradient k).lo.natAbs ((computed denominator ibox87).gradient k).hi.natAbs : Int)*((ibox87 k).hi-(ibox87 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox87
    (computed denominator ibox87) (computed denominator (FixedTape.midBox ibox87))
    (by decide +kernel)
private theorem midpoint_even_87 : ∀ k, 2 ∣ (ibox87 k).lo+(ibox87 k).hi := by decide +kernel
private theorem accepted_87 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox87) tree87 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox87 midpoint_even_87
  simp only [tree87,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox87,candidate_valid h (FixedTape.midBox ibox87),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox87 113 (FixedTape.rowsAux denominator ibox87 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox87) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_87
private noncomputable def tree86 : TapeTree := .split 0 (((1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree87 tree88
attribute [irreducible] tree86
private theorem accepted_86 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox86) tree86 = true := by
  simp only [tree86,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox86 0 (1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) false,decode_split denominator ibox86 0 (1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_87 h,accepted_88 h⟩
private noncomputable def tree85 : TapeTree := .centered (candidateRows ibox85) (candidateRows (FixedTape.midBox ibox85))
attribute [irreducible] tree85
private theorem sign_85 : 2*denominator*(computed denominator (FixedTape.midBox ibox85)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox85).gradient k).lo.natAbs ((computed denominator ibox85).gradient k).hi.natAbs : Int)*((ibox85 k).hi-(ibox85 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox85
    (computed denominator ibox85) (computed denominator (FixedTape.midBox ibox85))
    (by decide +kernel)
private theorem midpoint_even_85 : ∀ k, 2 ∣ (ibox85 k).lo+(ibox85 k).hi := by decide +kernel
private theorem accepted_85 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox85) tree85 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox85 midpoint_even_85
  simp only [tree85,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox85,candidate_valid h (FixedTape.midBox ibox85),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox85 113 (FixedTape.rowsAux denominator ibox85 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox85) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_85
private noncomputable def tree84 : TapeTree := .centered (candidateRows ibox84) (candidateRows (FixedTape.midBox ibox84))
attribute [irreducible] tree84
private theorem sign_84 : 2*denominator*(computed denominator (FixedTape.midBox ibox84)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox84).gradient k).lo.natAbs ((computed denominator ibox84).gradient k).hi.natAbs : Int)*((ibox84 k).hi-(ibox84 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox84
    (computed denominator ibox84) (computed denominator (FixedTape.midBox ibox84))
    (by decide +kernel)
private theorem midpoint_even_84 : ∀ k, 2 ∣ (ibox84 k).lo+(ibox84 k).hi := by decide +kernel
private theorem accepted_84 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox84) tree84 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox84 midpoint_even_84
  simp only [tree84,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox84,candidate_valid h (FixedTape.midBox ibox84),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox84 113 (FixedTape.rowsAux denominator ibox84 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox84) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_84
private noncomputable def tree83 : TapeTree := .split 0 (((1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree84 tree85
attribute [irreducible] tree83
private theorem accepted_83 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox83) tree83 = true := by
  simp only [tree83,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox83 0 (1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) false,decode_split denominator ibox83 0 (1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_84 h,accepted_85 h⟩
private noncomputable def tree82 : TapeTree := .split 2 (((191742730484984263926765613638645610842187941300753471907664960579174400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree83 tree86
attribute [irreducible] tree82
private theorem accepted_82 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox82) tree82 = true := by
  simp only [tree82,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox82 2 (191742730484984263926765613638645610842187941300753471907664960579174400000000000000000000000 : Int) false,decode_split denominator ibox82 2 (191742730484984263926765613638645610842187941300753471907664960579174400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_83 h,accepted_86 h⟩
private noncomputable def tree81 : TapeTree := .centered (candidateRows ibox81) (candidateRows (FixedTape.midBox ibox81))
attribute [irreducible] tree81
private theorem sign_81 : 2*denominator*(computed denominator (FixedTape.midBox ibox81)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox81).gradient k).lo.natAbs ((computed denominator ibox81).gradient k).hi.natAbs : Int)*((ibox81 k).hi-(ibox81 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox81
    (computed denominator ibox81) (computed denominator (FixedTape.midBox ibox81))
    (by decide +kernel)
private theorem midpoint_even_81 : ∀ k, 2 ∣ (ibox81 k).lo+(ibox81 k).hi := by decide +kernel
private theorem accepted_81 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox81) tree81 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox81 midpoint_even_81
  simp only [tree81,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox81,candidate_valid h (FixedTape.midBox ibox81),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox81 113 (FixedTape.rowsAux denominator ibox81 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox81) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_81
private noncomputable def tree80 : TapeTree := .centered (candidateRows ibox80) (candidateRows (FixedTape.midBox ibox80))
attribute [irreducible] tree80
private theorem sign_80 : 2*denominator*(computed denominator (FixedTape.midBox ibox80)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox80).gradient k).lo.natAbs ((computed denominator ibox80).gradient k).hi.natAbs : Int)*((ibox80 k).hi-(ibox80 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox80
    (computed denominator ibox80) (computed denominator (FixedTape.midBox ibox80))
    (by decide +kernel)
private theorem midpoint_even_80 : ∀ k, 2 ∣ (ibox80 k).lo+(ibox80 k).hi := by decide +kernel
private theorem accepted_80 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox80) tree80 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox80 midpoint_even_80
  simp only [tree80,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox80,candidate_valid h (FixedTape.midBox ibox80),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox80 113 (FixedTape.rowsAux denominator ibox80 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox80) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_80
private noncomputable def tree79 : TapeTree := .centered (candidateRows ibox79) (candidateRows (FixedTape.midBox ibox79))
attribute [irreducible] tree79
private theorem sign_79 : 2*denominator*(computed denominator (FixedTape.midBox ibox79)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox79).gradient k).lo.natAbs ((computed denominator ibox79).gradient k).hi.natAbs : Int)*((ibox79 k).hi-(ibox79 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox79
    (computed denominator ibox79) (computed denominator (FixedTape.midBox ibox79))
    (by decide +kernel)
private theorem midpoint_even_79 : ∀ k, 2 ∣ (ibox79 k).lo+(ibox79 k).hi := by decide +kernel
private theorem accepted_79 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox79) tree79 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox79 midpoint_even_79
  simp only [tree79,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox79,candidate_valid h (FixedTape.midBox ibox79),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox79 113 (FixedTape.rowsAux denominator ibox79 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox79) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_79
private noncomputable def tree78 : TapeTree := .split 0 (((1571225152585287786463966839755528707251258257177391472021300333902802456058652650373120000000 : Int) : ℚ)/(denominator : ℚ)) tree79 tree80
attribute [irreducible] tree78
private theorem accepted_78 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox78) tree78 = true := by
  simp only [tree78,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox78 0 (1571225152585287786463966839755528707251258257177391472021300333902802456058652650373120000000 : Int) false,decode_split denominator ibox78 0 (1571225152585287786463966839755528707251258257177391472021300333902802456058652650373120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_79 h,accepted_80 h⟩
private noncomputable def tree77 : TapeTree := .split 2 (((95871365242492131963382806819322805421093970650376735953832480289587200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree78 tree81
attribute [irreducible] tree77
private theorem accepted_77 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox77) tree77 = true := by
  simp only [tree77,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox77 2 (95871365242492131963382806819322805421093970650376735953832480289587200000000000000000000000 : Int) false,decode_split denominator ibox77 2 (95871365242492131963382806819322805421093970650376735953832480289587200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_78 h,accepted_81 h⟩
private noncomputable def tree76 : TapeTree := .centered (candidateRows ibox76) (candidateRows (FixedTape.midBox ibox76))
attribute [irreducible] tree76
private theorem sign_76 : 2*denominator*(computed denominator (FixedTape.midBox ibox76)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox76).gradient k).lo.natAbs ((computed denominator ibox76).gradient k).hi.natAbs : Int)*((ibox76 k).hi-(ibox76 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox76
    (computed denominator ibox76) (computed denominator (FixedTape.midBox ibox76))
    (by decide +kernel)
private theorem midpoint_even_76 : ∀ k, 2 ∣ (ibox76 k).lo+(ibox76 k).hi := by decide +kernel
private theorem accepted_76 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox76) tree76 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox76 midpoint_even_76
  simp only [tree76,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox76,candidate_valid h (FixedTape.midBox ibox76),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox76 113 (FixedTape.rowsAux denominator ibox76 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox76) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_76
private noncomputable def tree75 : TapeTree := .centered (candidateRows ibox75) (candidateRows (FixedTape.midBox ibox75))
attribute [irreducible] tree75
private theorem sign_75 : 2*denominator*(computed denominator (FixedTape.midBox ibox75)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox75).gradient k).lo.natAbs ((computed denominator ibox75).gradient k).hi.natAbs : Int)*((ibox75 k).hi-(ibox75 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox75
    (computed denominator ibox75) (computed denominator (FixedTape.midBox ibox75))
    (by decide +kernel)
private theorem midpoint_even_75 : ∀ k, 2 ∣ (ibox75 k).lo+(ibox75 k).hi := by decide +kernel
private theorem accepted_75 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox75) tree75 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox75 midpoint_even_75
  simp only [tree75,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox75,candidate_valid h (FixedTape.midBox ibox75),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox75 113 (FixedTape.rowsAux denominator ibox75 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox75) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_75
private noncomputable def tree74 : TapeTree := .centered (candidateRows ibox74) (candidateRows (FixedTape.midBox ibox74))
attribute [irreducible] tree74
private theorem sign_74 : 2*denominator*(computed denominator (FixedTape.midBox ibox74)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox74).gradient k).lo.natAbs ((computed denominator ibox74).gradient k).hi.natAbs : Int)*((ibox74 k).hi-(ibox74 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox74
    (computed denominator ibox74) (computed denominator (FixedTape.midBox ibox74))
    (by decide +kernel)
private theorem midpoint_even_74 : ∀ k, 2 ∣ (ibox74 k).lo+(ibox74 k).hi := by decide +kernel
private theorem accepted_74 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox74) tree74 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox74 midpoint_even_74
  simp only [tree74,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox74,candidate_valid h (FixedTape.midBox ibox74),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox74 113 (FixedTape.rowsAux denominator ibox74 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox74) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_74
private noncomputable def tree73 : TapeTree := .split 0 (((1560572778669455191006538183009016269837811450734915235803894022223712743941347349626880000000 : Int) : ℚ)/(denominator : ℚ)) tree74 tree75
attribute [irreducible] tree73
private theorem accepted_73 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox73) tree73 = true := by
  simp only [tree73,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox73 0 (1560572778669455191006538183009016269837811450734915235803894022223712743941347349626880000000 : Int) false,decode_split denominator ibox73 0 (1560572778669455191006538183009016269837811450734915235803894022223712743941347349626880000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_74 h,accepted_75 h⟩
private noncomputable def tree72 : TapeTree := .split 2 (((95871365242492131963382806819322805421093970650376735953832480289587200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree73 tree76
attribute [irreducible] tree72
private theorem accepted_72 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox72) tree72 = true := by
  simp only [tree72,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox72 2 (95871365242492131963382806819322805421093970650376735953832480289587200000000000000000000000 : Int) false,decode_split denominator ibox72 2 (95871365242492131963382806819322805421093970650376735953832480289587200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_73 h,accepted_76 h⟩
private noncomputable def tree71 : TapeTree := .split 0 (((1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree72 tree77
attribute [irreducible] tree71
private theorem accepted_71 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox71) tree71 = true := by
  simp only [tree71,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox71 0 (1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) false,decode_split denominator ibox71 0 (1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_72 h,accepted_77 h⟩
private noncomputable def tree70 : TapeTree := .centered (candidateRows ibox70) (candidateRows (FixedTape.midBox ibox70))
attribute [irreducible] tree70
private theorem sign_70 : 2*denominator*(computed denominator (FixedTape.midBox ibox70)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox70).gradient k).lo.natAbs ((computed denominator ibox70).gradient k).hi.natAbs : Int)*((ibox70 k).hi-(ibox70 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox70
    (computed denominator ibox70) (computed denominator (FixedTape.midBox ibox70))
    (by decide +kernel)
private theorem midpoint_even_70 : ∀ k, 2 ∣ (ibox70 k).lo+(ibox70 k).hi := by decide +kernel
private theorem accepted_70 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox70) tree70 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox70 midpoint_even_70
  simp only [tree70,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox70,candidate_valid h (FixedTape.midBox ibox70),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox70 113 (FixedTape.rowsAux denominator ibox70 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox70) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_70
private noncomputable def tree69 : TapeTree := .centered (candidateRows ibox69) (candidateRows (FixedTape.midBox ibox69))
attribute [irreducible] tree69
private theorem sign_69 : 2*denominator*(computed denominator (FixedTape.midBox ibox69)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox69).gradient k).lo.natAbs ((computed denominator ibox69).gradient k).hi.natAbs : Int)*((ibox69 k).hi-(ibox69 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox69
    (computed denominator ibox69) (computed denominator (FixedTape.midBox ibox69))
    (by decide +kernel)
private theorem midpoint_even_69 : ∀ k, 2 ∣ (ibox69 k).lo+(ibox69 k).hi := by decide +kernel
private theorem accepted_69 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox69) tree69 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox69 midpoint_even_69
  simp only [tree69,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox69,candidate_valid h (FixedTape.midBox ibox69),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox69 113 (FixedTape.rowsAux denominator ibox69 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox69) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_69
private noncomputable def tree68 : TapeTree := .split 0 (((1571225152585287786463966839755528707251258257177391472021300333902802456058652650373120000000 : Int) : ℚ)/(denominator : ℚ)) tree69 tree70
attribute [irreducible] tree68
private theorem accepted_68 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox68) tree68 = true := by
  simp only [tree68,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox68 0 (1571225152585287786463966839755528707251258257177391472021300333902802456058652650373120000000 : Int) false,decode_split denominator ibox68 0 (1571225152585287786463966839755528707251258257177391472021300333902802456058652650373120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_69 h,accepted_70 h⟩
private noncomputable def tree67 : TapeTree := .centered (candidateRows ibox67) (candidateRows (FixedTape.midBox ibox67))
attribute [irreducible] tree67
private theorem sign_67 : 2*denominator*(computed denominator (FixedTape.midBox ibox67)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox67).gradient k).lo.natAbs ((computed denominator ibox67).gradient k).hi.natAbs : Int)*((ibox67 k).hi-(ibox67 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox67
    (computed denominator ibox67) (computed denominator (FixedTape.midBox ibox67))
    (by decide +kernel)
private theorem midpoint_even_67 : ∀ k, 2 ∣ (ibox67 k).lo+(ibox67 k).hi := by decide +kernel
private theorem accepted_67 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox67) tree67 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox67 midpoint_even_67
  simp only [tree67,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox67,candidate_valid h (FixedTape.midBox ibox67),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox67 113 (FixedTape.rowsAux denominator ibox67 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox67) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_67
private noncomputable def tree66 : TapeTree := .centered (candidateRows ibox66) (candidateRows (FixedTape.midBox ibox66))
attribute [irreducible] tree66
private theorem sign_66 : 2*denominator*(computed denominator (FixedTape.midBox ibox66)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox66).gradient k).lo.natAbs ((computed denominator ibox66).gradient k).hi.natAbs : Int)*((ibox66 k).hi-(ibox66 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox66
    (computed denominator ibox66) (computed denominator (FixedTape.midBox ibox66))
    (by decide +kernel)
private theorem midpoint_even_66 : ∀ k, 2 ∣ (ibox66 k).lo+(ibox66 k).hi := by decide +kernel
private theorem accepted_66 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox66) tree66 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox66 midpoint_even_66
  simp only [tree66,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox66,candidate_valid h (FixedTape.midBox ibox66),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox66 113 (FixedTape.rowsAux denominator ibox66 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox66) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_66
private noncomputable def tree65 : TapeTree := .split 0 (((1573888246064245935328324003942156816604619958788010531075651911822574884087978975559680000000 : Int) : ℚ)/(denominator : ℚ)) tree66 tree67
attribute [irreducible] tree65
private theorem accepted_65 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox65) tree65 = true := by
  simp only [tree65,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox65 0 (1573888246064245935328324003942156816604619958788010531075651911822574884087978975559680000000 : Int) false,decode_split denominator ibox65 0 (1573888246064245935328324003942156816604619958788010531075651911822574884087978975559680000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_66 h,accepted_67 h⟩
private noncomputable def tree64 : TapeTree := .face 2 false (candidateRows ibox64) tree65
attribute [irreducible] tree64
private theorem sign_64 : ((computed denominator ibox64).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_64 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox64) tree64 = true := by
  simp only [tree64,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox64,?_,accepted_65 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox64)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox64).gradient 2).hi) denominator_positive).1 sign_64
private noncomputable def tree63 : TapeTree := .centered (candidateRows ibox63) (candidateRows (FixedTape.midBox ibox63))
attribute [irreducible] tree63
private theorem sign_63 : 2*denominator*(computed denominator (FixedTape.midBox ibox63)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox63).gradient k).lo.natAbs ((computed denominator ibox63).gradient k).hi.natAbs : Int)*((ibox63 k).hi-(ibox63 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox63
    (computed denominator ibox63) (computed denominator (FixedTape.midBox ibox63))
    (by decide +kernel)
private theorem midpoint_even_63 : ∀ k, 2 ∣ (ibox63 k).lo+(ibox63 k).hi := by decide +kernel
private theorem accepted_63 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox63) tree63 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox63 midpoint_even_63
  simp only [tree63,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox63,candidate_valid h (FixedTape.midBox ibox63),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox63 113 (FixedTape.rowsAux denominator ibox63 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox63) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_63
private noncomputable def tree62 : TapeTree := .centered (candidateRows ibox62) (candidateRows (FixedTape.midBox ibox62))
attribute [irreducible] tree62
private theorem sign_62 : 2*denominator*(computed denominator (FixedTape.midBox ibox62)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox62).gradient k).lo.natAbs ((computed denominator ibox62).gradient k).hi.natAbs : Int)*((ibox62 k).hi-(ibox62 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox62
    (computed denominator ibox62) (computed denominator (FixedTape.midBox ibox62))
    (by decide +kernel)
private theorem midpoint_even_62 : ∀ k, 2 ∣ (ibox62 k).lo+(ibox62 k).hi := by decide +kernel
private theorem accepted_62 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox62) tree62 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox62 midpoint_even_62
  simp only [tree62,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox62,candidate_valid h (FixedTape.midBox ibox62),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox62 113 (FixedTape.rowsAux denominator ibox62 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox62) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_62
private noncomputable def tree61 : TapeTree := .split 0 (((1568562059106329637599609675568900597897896555566772412966948755983030028029326325186560000000 : Int) : ℚ)/(denominator : ℚ)) tree62 tree63
attribute [irreducible] tree61
private theorem accepted_61 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox61) tree61 = true := by
  simp only [tree61,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox61 0 (1568562059106329637599609675568900597897896555566772412966948755983030028029326325186560000000 : Int) false,decode_split denominator ibox61 0 (1568562059106329637599609675568900597897896555566772412966948755983030028029326325186560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_62 h,accepted_63 h⟩
private noncomputable def tree60 : TapeTree := .face 2 false (candidateRows ibox60) tree61
attribute [irreducible] tree60
private theorem sign_60 : ((computed denominator ibox60).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_60 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox60) tree60 = true := by
  simp only [tree60,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox60,?_,accepted_61 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox60)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox60).gradient 2).hi) denominator_positive).1 sign_60
private noncomputable def tree59 : TapeTree := .split 0 (((1571225152585287786463966839755528707251258257177391472021300333902802456058652650373120000000 : Int) : ℚ)/(denominator : ℚ)) tree60 tree64
attribute [irreducible] tree59
private theorem accepted_59 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox59) tree59 = true := by
  simp only [tree59,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox59 0 (1571225152585287786463966839755528707251258257177391472021300333902802456058652650373120000000 : Int) false,decode_split denominator ibox59 0 (1571225152585287786463966839755528707251258257177391472021300333902802456058652650373120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_60 h,accepted_64 h⟩
private noncomputable def tree58 : TapeTree := .split 2 (((31957121747497377321127602273107601807031323550125578651277493429862400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree59 tree68
attribute [irreducible] tree58
private theorem accepted_58 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox58) tree58 = true := by
  simp only [tree58,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox58 2 (31957121747497377321127602273107601807031323550125578651277493429862400000000000000000000000 : Int) false,decode_split denominator ibox58 2 (31957121747497377321127602273107601807031323550125578651277493429862400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_59 h,accepted_68 h⟩
private noncomputable def tree57 : TapeTree := .centered (candidateRows ibox57) (candidateRows (FixedTape.midBox ibox57))
attribute [irreducible] tree57
private theorem sign_57 : 2*denominator*(computed denominator (FixedTape.midBox ibox57)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox57).gradient k).lo.natAbs ((computed denominator ibox57).gradient k).hi.natAbs : Int)*((ibox57 k).hi-(ibox57 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox57
    (computed denominator ibox57) (computed denominator (FixedTape.midBox ibox57))
    (by decide +kernel)
private theorem midpoint_even_57 : ∀ k, 2 ∣ (ibox57 k).lo+(ibox57 k).hi := by decide +kernel
private theorem accepted_57 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox57) tree57 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox57 midpoint_even_57
  simp only [tree57,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox57,candidate_valid h (FixedTape.midBox ibox57),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox57 113 (FixedTape.rowsAux denominator ibox57 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox57) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_57
private noncomputable def tree56 : TapeTree := .centered (candidateRows ibox56) (candidateRows (FixedTape.midBox ibox56))
attribute [irreducible] tree56
private theorem sign_56 : 2*denominator*(computed denominator (FixedTape.midBox ibox56)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox56).gradient k).lo.natAbs ((computed denominator ibox56).gradient k).hi.natAbs : Int)*((ibox56 k).hi-(ibox56 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox56
    (computed denominator ibox56) (computed denominator (FixedTape.midBox ibox56))
    (by decide +kernel)
private theorem midpoint_even_56 : ∀ k, 2 ∣ (ibox56 k).lo+(ibox56 k).hi := by decide +kernel
private theorem accepted_56 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox56) tree56 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox56 midpoint_even_56
  simp only [tree56,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox56,candidate_valid h (FixedTape.midBox ibox56),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox56 113 (FixedTape.rowsAux denominator ibox56 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox56) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_56
private noncomputable def tree55 : TapeTree := .split 0 (((1560572778669455191006538183009016269837811450734915235803894022223712743941347349626880000000 : Int) : ℚ)/(denominator : ℚ)) tree56 tree57
attribute [irreducible] tree55
private theorem accepted_55 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox55) tree55 = true := by
  simp only [tree55,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox55 0 (1560572778669455191006538183009016269837811450734915235803894022223712743941347349626880000000 : Int) false,decode_split denominator ibox55 0 (1560572778669455191006538183009016269837811450734915235803894022223712743941347349626880000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_56 h,accepted_57 h⟩
private noncomputable def tree54 : TapeTree := .centered (candidateRows ibox54) (candidateRows (FixedTape.midBox ibox54))
attribute [irreducible] tree54
private theorem sign_54 : 2*denominator*(computed denominator (FixedTape.midBox ibox54)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox54).gradient k).lo.natAbs ((computed denominator ibox54).gradient k).hi.natAbs : Int)*((ibox54 k).hi-(ibox54 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox54
    (computed denominator ibox54) (computed denominator (FixedTape.midBox ibox54))
    (by decide +kernel)
private theorem midpoint_even_54 : ∀ k, 2 ∣ (ibox54 k).lo+(ibox54 k).hi := by decide +kernel
private theorem accepted_54 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox54) tree54 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox54 midpoint_even_54
  simp only [tree54,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox54,candidate_valid h (FixedTape.midBox ibox54),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox54 113 (FixedTape.rowsAux denominator ibox54 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox54) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_54
private noncomputable def tree53 : TapeTree := .centered (candidateRows ibox53) (candidateRows (FixedTape.midBox ibox53))
attribute [irreducible] tree53
private theorem sign_53 : 2*denominator*(computed denominator (FixedTape.midBox ibox53)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox53).gradient k).lo.natAbs ((computed denominator ibox53).gradient k).hi.natAbs : Int)*((ibox53 k).hi-(ibox53 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox53
    (computed denominator ibox53) (computed denominator (FixedTape.midBox ibox53))
    (by decide +kernel)
private theorem midpoint_even_53 : ∀ k, 2 ∣ (ibox53 k).lo+(ibox53 k).hi := by decide +kernel
private theorem accepted_53 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox53) tree53 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox53 midpoint_even_53
  simp only [tree53,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox53,candidate_valid h (FixedTape.midBox ibox53),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox53 113 (FixedTape.rowsAux denominator ibox53 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox53) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_53
private noncomputable def tree52 : TapeTree := .split 0 (((1563235872148413339870895347195644379191173152345534294858245600143485171970673674813440000000 : Int) : ℚ)/(denominator : ℚ)) tree53 tree54
attribute [irreducible] tree52
private theorem accepted_52 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox52) tree52 = true := by
  simp only [tree52,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox52 0 (1563235872148413339870895347195644379191173152345534294858245600143485171970673674813440000000 : Int) false,decode_split denominator ibox52 0 (1563235872148413339870895347195644379191173152345534294858245600143485171970673674813440000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_53 h,accepted_54 h⟩
private noncomputable def tree51 : TapeTree := .face 2 false (candidateRows ibox51) tree52
attribute [irreducible] tree51
private theorem sign_51 : ((computed denominator ibox51).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_51 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox51) tree51 = true := by
  simp only [tree51,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox51,?_,accepted_52 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox51)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox51).gradient 2).hi) denominator_positive).1 sign_51
private noncomputable def tree50 : TapeTree := .centered (candidateRows ibox50) (candidateRows (FixedTape.midBox ibox50))
attribute [irreducible] tree50
private theorem sign_50 : 2*denominator*(computed denominator (FixedTape.midBox ibox50)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox50).gradient k).lo.natAbs ((computed denominator ibox50).gradient k).hi.natAbs : Int)*((ibox50 k).hi-(ibox50 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox50
    (computed denominator ibox50) (computed denominator (FixedTape.midBox ibox50))
    (by decide +kernel)
private theorem midpoint_even_50 : ∀ k, 2 ∣ (ibox50 k).lo+(ibox50 k).hi := by decide +kernel
private theorem accepted_50 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox50) tree50 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox50 midpoint_even_50
  simp only [tree50,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox50,candidate_valid h (FixedTape.midBox ibox50),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox50 113 (FixedTape.rowsAux denominator ibox50 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox50) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_50
private noncomputable def tree49 : TapeTree := .centered (candidateRows ibox49) (candidateRows (FixedTape.midBox ibox49))
attribute [irreducible] tree49
private theorem sign_49 : 2*denominator*(computed denominator (FixedTape.midBox ibox49)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox49).gradient k).lo.natAbs ((computed denominator ibox49).gradient k).hi.natAbs : Int)*((ibox49 k).hi-(ibox49 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox49
    (computed denominator ibox49) (computed denominator (FixedTape.midBox ibox49))
    (by decide +kernel)
private theorem midpoint_even_49 : ∀ k, 2 ∣ (ibox49 k).lo+(ibox49 k).hi := by decide +kernel
private theorem accepted_49 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox49) tree49 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox49 midpoint_even_49
  simp only [tree49,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox49,candidate_valid h (FixedTape.midBox ibox49),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox49 113 (FixedTape.rowsAux denominator ibox49 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox49) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_49
private noncomputable def tree48 : TapeTree := .split 0 (((1557909685190497042142181018822388160484449749124296176749542444303940315912021024440320000000 : Int) : ℚ)/(denominator : ℚ)) tree49 tree50
attribute [irreducible] tree48
private theorem accepted_48 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox48) tree48 = true := by
  simp only [tree48,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox48 0 (1557909685190497042142181018822388160484449749124296176749542444303940315912021024440320000000 : Int) false,decode_split denominator ibox48 0 (1557909685190497042142181018822388160484449749124296176749542444303940315912021024440320000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_49 h,accepted_50 h⟩
private noncomputable def tree47 : TapeTree := .face 2 false (candidateRows ibox47) tree48
attribute [irreducible] tree47
private theorem sign_47 : ((computed denominator ibox47).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_47 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox47) tree47 = true := by
  simp only [tree47,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox47,?_,accepted_48 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox47)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox47).gradient 2).hi) denominator_positive).1 sign_47
private noncomputable def tree46 : TapeTree := .split 0 (((1560572778669455191006538183009016269837811450734915235803894022223712743941347349626880000000 : Int) : ℚ)/(denominator : ℚ)) tree47 tree51
attribute [irreducible] tree46
private theorem accepted_46 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox46) tree46 = true := by
  simp only [tree46,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox46 0 (1560572778669455191006538183009016269837811450734915235803894022223712743941347349626880000000 : Int) false,decode_split denominator ibox46 0 (1560572778669455191006538183009016269837811450734915235803894022223712743941347349626880000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_47 h,accepted_51 h⟩
private noncomputable def tree45 : TapeTree := .split 2 (((31957121747497377321127602273107601807031323550125578651277493429862400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree46 tree55
attribute [irreducible] tree45
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox45 2 (31957121747497377321127602273107601807031323550125578651277493429862400000000000000000000000 : Int) false,decode_split denominator ibox45 2 (31957121747497377321127602273107601807031323550125578651277493429862400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_46 h,accepted_55 h⟩
private noncomputable def tree44 : TapeTree := .split 0 (((1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree45 tree58
attribute [irreducible] tree44
private theorem accepted_44 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox44) tree44 = true := by
  simp only [tree44,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox44 0 (1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) false,decode_split denominator ibox44 0 (1565898965627371488735252511382272488544534853956153353912597178063257600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_45 h,accepted_58 h⟩
private noncomputable def tree43 : TapeTree := .split 2 (((63914243494994754642255204546215203614062647100251157302554986859724800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree44 tree71
attribute [irreducible] tree43
private theorem accepted_43 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox43) tree43 = true := by
  simp only [tree43,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox43 2 (63914243494994754642255204546215203614062647100251157302554986859724800000000000000000000000 : Int) false,decode_split denominator ibox43 2 (63914243494994754642255204546215203614062647100251157302554986859724800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_44 h,accepted_71 h⟩
private noncomputable def tree42 : TapeTree := .split 2 (((127828486989989509284510409092430407228125294200502314605109973719449600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree43 tree82
attribute [irreducible] tree42
private theorem accepted_42 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox42) tree42 = true := by
  simp only [tree42,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox42 2 (127828486989989509284510409092430407228125294200502314605109973719449600000000000000000000000 : Int) false,decode_split denominator ibox42 2 (127828486989989509284510409092430407228125294200502314605109973719449600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_43 h,accepted_82 h⟩
private noncomputable def tree41 : TapeTree := .face 1 true (candidateRows ibox41) tree42
attribute [irreducible] tree41
private theorem sign_41 : 0 ≤ ((computed denominator ibox41).gradient 1).lo := by decide +kernel
private theorem accepted_41 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox41) tree41 = true := by
  simp only [tree41,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox41,?_,accepted_42 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox41)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox41).gradient 1).lo) denominator_positive).2 sign_41
private noncomputable def tree40 : TapeTree := .split 2 (((255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree41 tree89
attribute [irreducible] tree40
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox40 2 (255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) false,decode_split denominator ibox40 2 (255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_41 h,accepted_89 h⟩
private noncomputable def tree39 : TapeTree := .centered (candidateRows ibox39) (candidateRows (FixedTape.midBox ibox39))
attribute [irreducible] tree39
private theorem sign_39 : 2*denominator*(computed denominator (FixedTape.midBox ibox39)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox39).gradient k).lo.natAbs ((computed denominator ibox39).gradient k).hi.natAbs : Int)*((ibox39 k).hi-(ibox39 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox39
    (computed denominator ibox39) (computed denominator (FixedTape.midBox ibox39))
    (by decide +kernel)
private theorem midpoint_even_39 : ∀ k, 2 ∣ (ibox39 k).lo+(ibox39 k).hi := by decide +kernel
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox39 midpoint_even_39
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox39,candidate_valid h (FixedTape.midBox ibox39),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox39 113 (FixedTape.rowsAux denominator ibox39 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox39) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_39
private noncomputable def tree38 : TapeTree := .centered (candidateRows ibox38) (candidateRows (FixedTape.midBox ibox38))
attribute [irreducible] tree38
private theorem sign_38 : 2*denominator*(computed denominator (FixedTape.midBox ibox38)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox38).gradient k).lo.natAbs ((computed denominator ibox38).gradient k).hi.natAbs : Int)*((ibox38 k).hi-(ibox38 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox38
    (computed denominator ibox38) (computed denominator (FixedTape.midBox ibox38))
    (by decide +kernel)
private theorem midpoint_even_38 : ∀ k, 2 ∣ (ibox38 k).lo+(ibox38 k).hi := by decide +kernel
private theorem accepted_38 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox38) tree38 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox38 midpoint_even_38
  simp only [tree38,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox38,candidate_valid h (FixedTape.midBox ibox38),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox38 113 (FixedTape.rowsAux denominator ibox38 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox38) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_38
private noncomputable def tree37 : TapeTree := .split 2 (((383485460969968527853531227277291221684375882601506943815329921158348800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree38 tree39
attribute [irreducible] tree37
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox37 2 (383485460969968527853531227277291221684375882601506943815329921158348800000000000000000000000 : Int) false,decode_split denominator ibox37 2 (383485460969968527853531227277291221684375882601506943815329921158348800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_38 h,accepted_39 h⟩
private noncomputable def tree36 : TapeTree := .centered (candidateRows ibox36) (candidateRows (FixedTape.midBox ibox36))
attribute [irreducible] tree36
private theorem sign_36 : 2*denominator*(computed denominator (FixedTape.midBox ibox36)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox36).gradient k).lo.natAbs ((computed denominator ibox36).gradient k).hi.natAbs : Int)*((ibox36 k).hi-(ibox36 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox36
    (computed denominator ibox36) (computed denominator (FixedTape.midBox ibox36))
    (by decide +kernel)
private theorem midpoint_even_36 : ∀ k, 2 ∣ (ibox36 k).lo+(ibox36 k).hi := by decide +kernel
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox36 midpoint_even_36
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox36,candidate_valid h (FixedTape.midBox ibox36),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox36 113 (FixedTape.rowsAux denominator ibox36 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox36) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_36
private noncomputable def tree35 : TapeTree := .split 1 (((1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree36 tree37
attribute [irreducible] tree35
private theorem accepted_35 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox35) tree35 = true := by
  simp only [tree35,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox35 1 (1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 : Int) false,decode_split denominator ibox35 1 (1661770330869863620698635318201595293965628824606530089866429658352844800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_36 h,accepted_37 h⟩
private noncomputable def tree34 : TapeTree := .centered (candidateRows ibox34) (candidateRows (FixedTape.midBox ibox34))
attribute [irreducible] tree34
private theorem sign_34 : 2*denominator*(computed denominator (FixedTape.midBox ibox34)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox34).gradient k).lo.natAbs ((computed denominator ibox34).gradient k).hi.natAbs : Int)*((ibox34 k).hi-(ibox34 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox34
    (computed denominator ibox34) (computed denominator (FixedTape.midBox ibox34))
    (by decide +kernel)
private theorem midpoint_even_34 : ∀ k, 2 ∣ (ibox34 k).lo+(ibox34 k).hi := by decide +kernel
private theorem accepted_34 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox34) tree34 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox34 midpoint_even_34
  simp only [tree34,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox34,candidate_valid h (FixedTape.midBox ibox34),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox34 113 (FixedTape.rowsAux denominator ibox34 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox34) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_34
private noncomputable def tree33 : TapeTree := .face 1 true (candidateRows ibox33) tree34
attribute [irreducible] tree33
private theorem sign_33 : 0 ≤ ((computed denominator ibox33).gradient 1).lo := by decide +kernel
private theorem accepted_33 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox33) tree33 = true := by
  simp only [tree33,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox33,?_,accepted_34 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox33)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox33).gradient 1).lo) denominator_positive).2 sign_33
private noncomputable def tree32 : TapeTree := .split 2 (((255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree33 tree35
attribute [irreducible] tree32
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox32 2 (255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) false,decode_split denominator ibox32 2 (255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_33 h,accepted_35 h⟩
private noncomputable def tree31 : TapeTree := .split 1 (((1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree32 tree40
attribute [irreducible] tree31
private theorem accepted_31 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox31) tree31 = true := by
  simp only [tree31,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox31 1 (1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) false,decode_split denominator ibox31 1 (1789598817859853129983145727294025701193754118807032404471539632072294400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_32 h,accepted_40 h⟩
private noncomputable def tree30 : TapeTree := .centered (candidateRows ibox30) (candidateRows (FixedTape.midBox ibox30))
attribute [irreducible] tree30
private theorem sign_30 : 2*denominator*(computed denominator (FixedTape.midBox ibox30)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox30).gradient k).lo.natAbs ((computed denominator ibox30).gradient k).hi.natAbs : Int)*((ibox30 k).hi-(ibox30 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox30
    (computed denominator ibox30) (computed denominator (FixedTape.midBox ibox30))
    (by decide +kernel)
private theorem midpoint_even_30 : ∀ k, 2 ∣ (ibox30 k).lo+(ibox30 k).hi := by decide +kernel
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox30 midpoint_even_30
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox30,candidate_valid h (FixedTape.midBox ibox30),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox30 113 (FixedTape.rowsAux denominator ibox30 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox30) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_30
private noncomputable def tree29 : TapeTree := .centered (candidateRows ibox29) (candidateRows (FixedTape.midBox ibox29))
attribute [irreducible] tree29
private theorem sign_29 : 2*denominator*(computed denominator (FixedTape.midBox ibox29)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox29).gradient k).lo.natAbs ((computed denominator ibox29).gradient k).hi.natAbs : Int)*((ibox29 k).hi-(ibox29 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox29
    (computed denominator ibox29) (computed denominator (FixedTape.midBox ibox29))
    (by decide +kernel)
private theorem midpoint_even_29 : ∀ k, 2 ∣ (ibox29 k).lo+(ibox29 k).hi := by decide +kernel
private theorem accepted_29 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox29) tree29 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox29 midpoint_even_29
  simp only [tree29,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox29,candidate_valid h (FixedTape.midBox ibox29),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox29 113 (FixedTape.rowsAux denominator ibox29 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox29) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_29
private noncomputable def tree28 : TapeTree := .split 2 (((255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree29 tree30
attribute [irreducible] tree28
private theorem accepted_28 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox28) tree28 = true := by
  simp only [tree28,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox28 2 (255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) false,decode_split denominator ibox28 2 (255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_29 h,accepted_30 h⟩
private noncomputable def tree27 : TapeTree := .centered (candidateRows ibox27) (candidateRows (FixedTape.midBox ibox27))
attribute [irreducible] tree27
private theorem sign_27 : 2*denominator*(computed denominator (FixedTape.midBox ibox27)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox27).gradient k).lo.natAbs ((computed denominator ibox27).gradient k).hi.natAbs : Int)*((ibox27 k).hi-(ibox27 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox27
    (computed denominator ibox27) (computed denominator (FixedTape.midBox ibox27))
    (by decide +kernel)
private theorem midpoint_even_27 : ∀ k, 2 ∣ (ibox27 k).lo+(ibox27 k).hi := by decide +kernel
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox27 midpoint_even_27
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox27,candidate_valid h (FixedTape.midBox ibox27),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox27 113 (FixedTape.rowsAux denominator ibox27 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox27) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_27
private noncomputable def tree26 : TapeTree := .centered (candidateRows ibox26) (candidateRows (FixedTape.midBox ibox26))
attribute [irreducible] tree26
private theorem sign_26 : 2*denominator*(computed denominator (FixedTape.midBox ibox26)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox26).gradient k).lo.natAbs ((computed denominator ibox26).gradient k).hi.natAbs : Int)*((ibox26 k).hi-(ibox26 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox26
    (computed denominator ibox26) (computed denominator (FixedTape.midBox ibox26))
    (by decide +kernel)
private theorem midpoint_even_26 : ∀ k, 2 ∣ (ibox26 k).lo+(ibox26 k).hi := by decide +kernel
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox26 midpoint_even_26
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox26,candidate_valid h (FixedTape.midBox ibox26),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox26 113 (FixedTape.rowsAux denominator ibox26 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox26) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_26
private noncomputable def tree25 : TapeTree := .split 2 (((255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree26 tree27
attribute [irreducible] tree25
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox25 2 (255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) false,decode_split denominator ibox25 2 (255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_26 h,accepted_27 h⟩
private noncomputable def tree24 : TapeTree := .split 1 (((1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree25 tree28
attribute [irreducible] tree24
private theorem accepted_24 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox24) tree24 = true := by
  simp only [tree24,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox24 1 (1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) false,decode_split denominator ibox24 1 (1278284869899895092845104090924304072281252942005023146051099737194496000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_25 h,accepted_28 h⟩
private noncomputable def tree23 : TapeTree := .split 1 (((1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree24 tree31
attribute [irreducible] tree23
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox23 1 (1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) false,decode_split denominator ibox23 1 (1533941843879874111414124909109164886737503530406027775261319684633395200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_24 h,accepted_31 h⟩
private noncomputable def tree22 : TapeTree := .split 2 (((511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree23 tree108
attribute [irreducible] tree22
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox22 2 (511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) false,decode_split denominator ibox22 2 (511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_23 h,accepted_108 h⟩
private noncomputable def tree21 : TapeTree := .centered (candidateRows ibox21) (candidateRows (FixedTape.midBox ibox21))
attribute [irreducible] tree21
private theorem sign_21 : 2*denominator*(computed denominator (FixedTape.midBox ibox21)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox21).gradient k).lo.natAbs ((computed denominator ibox21).gradient k).hi.natAbs : Int)*((ibox21 k).hi-(ibox21 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox21
    (computed denominator ibox21) (computed denominator (FixedTape.midBox ibox21))
    (by decide +kernel)
private theorem midpoint_even_21 : ∀ k, 2 ∣ (ibox21 k).lo+(ibox21 k).hi := by decide +kernel
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox21 midpoint_even_21
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox21,candidate_valid h (FixedTape.midBox ibox21),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox21 113 (FixedTape.rowsAux denominator ibox21 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox21) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_21
private noncomputable def tree20 : TapeTree := .centered (candidateRows ibox20) (candidateRows (FixedTape.midBox ibox20))
attribute [irreducible] tree20
private theorem sign_20 : 2*denominator*(computed denominator (FixedTape.midBox ibox20)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox20).gradient k).lo.natAbs ((computed denominator ibox20).gradient k).hi.natAbs : Int)*((ibox20 k).hi-(ibox20 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox20
    (computed denominator ibox20) (computed denominator (FixedTape.midBox ibox20))
    (by decide +kernel)
private theorem midpoint_even_20 : ∀ k, 2 ∣ (ibox20 k).lo+(ibox20 k).hi := by decide +kernel
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox20 midpoint_even_20
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox20,candidate_valid h (FixedTape.midBox ibox20),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox20 113 (FixedTape.rowsAux denominator ibox20 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox20) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_20
private noncomputable def tree19 : TapeTree := .split 1 (((766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree21
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 1 (766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) false,decode_split denominator ibox19 1 (766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_20 h,accepted_21 h⟩
private noncomputable def tree18 : TapeTree := .centered (candidateRows ibox18) (candidateRows (FixedTape.midBox ibox18))
attribute [irreducible] tree18
private theorem sign_18 : 2*denominator*(computed denominator (FixedTape.midBox ibox18)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox18).gradient k).lo.natAbs ((computed denominator ibox18).gradient k).hi.natAbs : Int)*((ibox18 k).hi-(ibox18 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox18
    (computed denominator ibox18) (computed denominator (FixedTape.midBox ibox18))
    (by decide +kernel)
private theorem midpoint_even_18 : ∀ k, 2 ∣ (ibox18 k).lo+(ibox18 k).hi := by decide +kernel
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox18 midpoint_even_18
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox18,candidate_valid h (FixedTape.midBox ibox18),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox18 113 (FixedTape.rowsAux denominator ibox18 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox18) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_18
private noncomputable def tree17 : TapeTree := .centered (candidateRows ibox17) (candidateRows (FixedTape.midBox ibox17))
attribute [irreducible] tree17
private theorem sign_17 : 2*denominator*(computed denominator (FixedTape.midBox ibox17)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox17).gradient k).lo.natAbs ((computed denominator ibox17).gradient k).hi.natAbs : Int)*((ibox17 k).hi-(ibox17 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox17
    (computed denominator ibox17) (computed denominator (FixedTape.midBox ibox17))
    (by decide +kernel)
private theorem midpoint_even_17 : ∀ k, 2 ∣ (ibox17 k).lo+(ibox17 k).hi := by decide +kernel
private theorem accepted_17 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox17) tree17 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox17 midpoint_even_17
  simp only [tree17,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox17,candidate_valid h (FixedTape.midBox ibox17),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox17 113 (FixedTape.rowsAux denominator ibox17 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox17) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_17
private noncomputable def tree16 : TapeTree := .split 1 (((766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree18
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 1 (766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) false,decode_split denominator ibox16 1 (766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_17 h,accepted_18 h⟩
private noncomputable def tree15 : TapeTree := .split 2 (((766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree16 tree19
attribute [irreducible] tree15
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox15 2 (766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) false,decode_split denominator ibox15 2 (766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_16 h,accepted_19 h⟩
private noncomputable def tree14 : TapeTree := .centered (candidateRows ibox14) (candidateRows (FixedTape.midBox ibox14))
attribute [irreducible] tree14
private theorem sign_14 : 2*denominator*(computed denominator (FixedTape.midBox ibox14)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox14).gradient k).lo.natAbs ((computed denominator ibox14).gradient k).hi.natAbs : Int)*((ibox14 k).hi-(ibox14 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox14
    (computed denominator ibox14) (computed denominator (FixedTape.midBox ibox14))
    (by decide +kernel)
private theorem midpoint_even_14 : ∀ k, 2 ∣ (ibox14 k).lo+(ibox14 k).hi := by decide +kernel
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox14 midpoint_even_14
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox14,candidate_valid h (FixedTape.midBox ibox14),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox14 113 (FixedTape.rowsAux denominator ibox14 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox14) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_14
private noncomputable def tree13 : TapeTree := .centered (candidateRows ibox13) (candidateRows (FixedTape.midBox ibox13))
attribute [irreducible] tree13
private theorem sign_13 : 2*denominator*(computed denominator (FixedTape.midBox ibox13)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox13).gradient k).lo.natAbs ((computed denominator ibox13).gradient k).hi.natAbs : Int)*((ibox13 k).hi-(ibox13 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox13
    (computed denominator ibox13) (computed denominator (FixedTape.midBox ibox13))
    (by decide +kernel)
private theorem midpoint_even_13 : ∀ k, 2 ∣ (ibox13 k).lo+(ibox13 k).hi := by decide +kernel
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox13 midpoint_even_13
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox13,candidate_valid h (FixedTape.midBox ibox13),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox13 113 (FixedTape.rowsAux denominator ibox13 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox13) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_13
private noncomputable def tree12 : TapeTree := .split 1 (((255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree13 tree14
attribute [irreducible] tree12
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox12 1 (255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) false,decode_split denominator ibox12 1 (255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_13 h,accepted_14 h⟩
private noncomputable def tree11 : TapeTree := .centered (candidateRows ibox11) (candidateRows (FixedTape.midBox ibox11))
attribute [irreducible] tree11
private theorem sign_11 : 2*denominator*(computed denominator (FixedTape.midBox ibox11)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox11).gradient k).lo.natAbs ((computed denominator ibox11).gradient k).hi.natAbs : Int)*((ibox11 k).hi-(ibox11 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox11
    (computed denominator ibox11) (computed denominator (FixedTape.midBox ibox11))
    (by decide +kernel)
private theorem midpoint_even_11 : ∀ k, 2 ∣ (ibox11 k).lo+(ibox11 k).hi := by decide +kernel
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox11 midpoint_even_11
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox11,candidate_valid h (FixedTape.midBox ibox11),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox11 113 (FixedTape.rowsAux denominator ibox11 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox11) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_11
private noncomputable def tree10 : TapeTree := .split 2 (((766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree11 tree12
attribute [irreducible] tree10
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox10 2 (766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) false,decode_split denominator ibox10 2 (766970921939937055707062454554582443368751765203013887630659842316697600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_11 h,accepted_12 h⟩
private noncomputable def tree9 : TapeTree := .split 1 (((511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree10 tree15
attribute [irreducible] tree9
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox9 1 (511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) false,decode_split denominator ibox9 1 (511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_10 h,accepted_15 h⟩
private noncomputable def tree8 : TapeTree := .centered (candidateRows ibox8) (candidateRows (FixedTape.midBox ibox8))
attribute [irreducible] tree8
private theorem sign_8 : 2*denominator*(computed denominator (FixedTape.midBox ibox8)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox8).gradient k).lo.natAbs ((computed denominator ibox8).gradient k).hi.natAbs : Int)*((ibox8 k).hi-(ibox8 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox8
    (computed denominator ibox8) (computed denominator (FixedTape.midBox ibox8))
    (by decide +kernel)
private theorem midpoint_even_8 : ∀ k, 2 ∣ (ibox8 k).lo+(ibox8 k).hi := by decide +kernel
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox8 midpoint_even_8
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox8,candidate_valid h (FixedTape.midBox ibox8),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox8 113 (FixedTape.rowsAux denominator ibox8 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox8) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_8
private noncomputable def tree7 : TapeTree := .centered (candidateRows ibox7) (candidateRows (FixedTape.midBox ibox7))
attribute [irreducible] tree7
private theorem sign_7 : 2*denominator*(computed denominator (FixedTape.midBox ibox7)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox7).gradient k).lo.natAbs ((computed denominator ibox7).gradient k).hi.natAbs : Int)*((ibox7 k).hi-(ibox7 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox7
    (computed denominator ibox7) (computed denominator (FixedTape.midBox ibox7))
    (by decide +kernel)
private theorem midpoint_even_7 : ∀ k, 2 ∣ (ibox7 k).lo+(ibox7 k).hi := by decide +kernel
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox7 midpoint_even_7
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox7,candidate_valid h (FixedTape.midBox ibox7),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox7 113 (FixedTape.rowsAux denominator ibox7 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox7) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_7
private noncomputable def tree6 : TapeTree := .split 2 (((255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree8
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 2 (255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) false,decode_split denominator ibox6 2 (255656973979979018569020818184860814456250588401004629210219947438899200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_7 h,accepted_8 h⟩
private noncomputable def tree5 : TapeTree := .centered (candidateRows ibox5) (candidateRows (FixedTape.midBox ibox5))
attribute [irreducible] tree5
private theorem sign_5 : 2*denominator*(computed denominator (FixedTape.midBox ibox5)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox5).gradient k).lo.natAbs ((computed denominator ibox5).gradient k).hi.natAbs : Int)*((ibox5 k).hi-(ibox5 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox5
    (computed denominator ibox5) (computed denominator (FixedTape.midBox ibox5))
    (by decide +kernel)
private theorem midpoint_even_5 : ∀ k, 2 ∣ (ibox5 k).lo+(ibox5 k).hi := by decide +kernel
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox5 midpoint_even_5
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox5,candidate_valid h (FixedTape.midBox ibox5),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox5 113 (FixedTape.rowsAux denominator ibox5 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox5) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_5
private noncomputable def tree4 : TapeTree := .split 1 (((511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree6
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 1 (511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) false,decode_split denominator ibox4 1 (511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_6 h⟩
private noncomputable def tree3 : TapeTree := .split 2 (((511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree9
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 2 (511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) false,decode_split denominator ibox3 2 (511313947959958037138041636369721628912501176802009258420439894877798400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_9 h⟩
private noncomputable def tree2 : TapeTree := .split 1 (((1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree22
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 1 (1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 : Int) false,decode_split denominator ibox2 1 (1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_22 h⟩
private noncomputable def tree1 : TapeTree := .split 2 (((1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree2 tree151
attribute [irreducible] tree1
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox1 2 (1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 : Int) false,decode_split denominator ibox1 2 (1022627895919916074276083272739443257825002353604018516840879789755596800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_2 h,accepted_151 h⟩
private noncomputable def tree0 : TapeTree := .face 3 true (candidateRows ibox0) tree1
attribute [irreducible] tree0
private theorem sign_0 : 0 ≤ ((computed denominator ibox0).gradient 3).lo := by decide +kernel
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox0,?_,accepted_1 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox0)).gradient 3).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox0).gradient 3).lo) denominator_positive).2 sign_0
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (3802083333333333/5000000000000000 : ℚ) (3854166666666667/5000000000000000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 113 = e123 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (3802083333333333/5000000000000000 : ℚ) (3854166666666667/5000000000000000 : ℚ)) x → eval e123 x ≤ 0 := by
  have hb := h.child_4 tape 113 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell103_high_internal_top

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell103_high_internal_top
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((3802083333333333/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((3854166666666667/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 103 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 103 p)
    (hkb : ((3854166666666667/5000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((3802083333333333/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : bStar < a), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell103_high_internal_top.cell_bound h.child_8 h.child_9 (Cell103_high_internal_top.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell103_high_internal_top
