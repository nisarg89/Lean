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
namespace Cell94_high_internal_top
private noncomputable def qValues : Fin 2 → ℚ := ![(10503975350491275697898327585575312876/9323494627643469402458983775858378367 : ℚ),(7877373407782038227315000000000000000/9323494627643469402458983775858378367 : ℚ)]
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
    priceLambda 94 p = ((10503975350491275697898327585575312876/9323494627643469402458983775858378367 : ℝ)+(7877373407782038227315000000000000000/9323494627643469402458983775858378367 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell94,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 94 p = 0 := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell94,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e123 x = (x 0*(1-x 0))*(aPoint x+priceLambda 94 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 94 (x 0)*psiStar (rPoint x)+(cStar-aPoint x-eta (0 : Fin 9)*psiStar (aPoint x))-(cStar-capPoint x-eta (0 : Fin 9)*psiStar (capPoint x))) := by
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
    (hL : lambdaStar (x 0) = priceLambda 94 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 94 (x 0)) :
    (1)*eval e123 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_neg (not_le.mpr ha),if_neg (not_le.mpr hA),hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (23/32 : ℚ) (3645833333333333/5000000000000000 : ℚ)) x → eval e123 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((23/32 : ℚ) : ℝ) < p ∧ p ≤ ((3645833333333333/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 94 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 94 p)
    (hkb : ((3645833333333333/5000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((23/32 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : bStar < a) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h7 (23/32 : ℚ) (3645833333333333/5000000000000000 : ℚ) bStar p a A r hpcell hkb hr.2 hap hcase hpA hAr
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 94 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 94 (x 0) := by simpa only [hxp] using hT
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
.const (10503975350491275697898327585575312876/9323494627643469402458983775858378367 : ℚ),
.const (7877373407782038227315000000000000000/9323494627643469402458983775858378367 : ℚ),
.mul 104 1,
.add 103 105,
.mul 1 10,
.add 8 38,
.neg 55,
.add 108 109,
.mul 110 107,
.mul 106 102,
.add 111 112]
private noncomputable def ssaQVals : Fin 15 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(-2840189/5000000 : ℚ),(113609/200000 : ℚ),(1085/4818 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ),(4818/3733 : ℚ),(145513/100000 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(10503975350491275697898327585575312876/9323494627643469402458983775858378367 : ℚ),(7877373407782038227315000000000000000/9323494627643469402458983775858378367 : ℚ)]
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
private noncomputable def denominator : Int := 40259572072035103366783788145287769057451644694597449573627508442110361600000000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000,29355937969192260187641707386932107152139281237292703150660411932542167091499437192642560000000⟩,⟨0,40259572072035103366783788145287769057451644694597449573627508442110361600000000000000000000000⟩,⟨0,40259572072035103366783788145287769057451644694597449573627508442110361600000000000000000000000⟩,⟨0,40259572072035103366783788145287769057451644694597449573627508442110361600000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 3 true
private noncomputable def ibox2 : Fin 4 → FixedTape.I := splitI ibox1 2 20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 1 20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 2 10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 1 10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox4 1 10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 true
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 2 5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox6 2 5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox3 2 10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox9 1 10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 false
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox10 2 15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 false
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox10 2 15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 true
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox12 2 17613562781515357722967907313563398962635094553886384188462034943423283200000000000000000000000 false
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox12 2 17613562781515357722967907313563398962635094553886384188462034943423283200000000000000000000000 true
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox9 1 10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 true
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox15 2 15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 false
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 1 15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox16 1 15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox15 2 15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 1 15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox19 1 15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 true
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox2 1 20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 true
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox22 2 10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 false
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox23 1 30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 false
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox24 2 5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 false
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox25 1 25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 false
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox25 1 25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 true
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox24 2 5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 true
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox28 1 25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 false
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox28 1 25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 true
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox30 1 27678455799524133564663854349885341226998005727535746581868912053950873600000000000000000000000 false
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox30 1 27678455799524133564663854349885341226998005727535746581868912053950873600000000000000000000000 true
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox23 1 30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 true
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox33 2 5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 false
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox34 1 35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 false
private noncomputable def ibox36 : Fin 4 → FixedTape.I := faceI ibox35 1 true
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox34 1 35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 true
private noncomputable def ibox38 : Fin 4 → FixedTape.I := faceI ibox37 1 true
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox38 2 2516223254502193960423986759080485566090727793412340598351719277631897600000000000000000000000 false
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox39 2 1258111627251096980211993379540242783045363896706170299175859638815948800000000000000000000000 false
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox40 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 false
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox41 2 629055813625548490105996689770121391522681948353085149587929819407974400000000000000000000000 false
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox42 0 29041410062379487955567312643802214795567347527504613448448681752710658572874859298160640000000 false
private noncomputable def ibox44 : Fin 4 → FixedTape.I := faceI ibox43 2 false
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox42 0 29041410062379487955567312643802214795567347527504613448448681752710658572874859298160640000000 true
private noncomputable def ibox46 : Fin 4 → FixedTape.I := faceI ibox45 2 false
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox41 2 629055813625548490105996689770121391522681948353085149587929819407974400000000000000000000000 true
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox47 0 29041410062379487955567312643802214795567347527504613448448681752710658572874859298160640000000 false
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox47 0 29041410062379487955567312643802214795567347527504613448448681752710658572874859298160640000000 true
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox40 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 true
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox50 2 629055813625548490105996689770121391522681948353085149587929819407974400000000000000000000000 false
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox51 0 29251095333588002776950242472555476366615303334030006583256501872598330918624577894481920000000 false
private noncomputable def ibox53 : Fin 4 → FixedTape.I := faceI ibox52 2 false
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox51 0 29251095333588002776950242472555476366615303334030006583256501872598330918624577894481920000000 true
private noncomputable def ibox55 : Fin 4 → FixedTape.I := faceI ibox54 2 false
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox50 2 629055813625548490105996689770121391522681948353085149587929819407974400000000000000000000000 true
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox56 0 29251095333588002776950242472555476366615303334030006583256501872598330918624577894481920000000 false
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox56 0 29251095333588002776950242472555476366615303334030006583256501872598330918624577894481920000000 true
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox39 2 1258111627251096980211993379540242783045363896706170299175859638815948800000000000000000000000 true
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox59 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 false
private noncomputable def ibox61 : Fin 4 → FixedTape.I := splitI ibox60 2 1887167440876645470317990069310364174568045845059255448763789458223923200000000000000000000000 false
private noncomputable def ibox62 : Fin 4 → FixedTape.I := splitI ibox61 0 29041410062379487955567312643802214795567347527504613448448681752710658572874859298160640000000 false
private noncomputable def ibox63 : Fin 4 → FixedTape.I := splitI ibox61 0 29041410062379487955567312643802214795567347527504613448448681752710658572874859298160640000000 true
private noncomputable def ibox64 : Fin 4 → FixedTape.I := splitI ibox60 2 1887167440876645470317990069310364174568045845059255448763789458223923200000000000000000000000 true
private noncomputable def ibox65 : Fin 4 → FixedTape.I := splitI ibox59 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 true
private noncomputable def ibox66 : Fin 4 → FixedTape.I := splitI ibox65 2 1887167440876645470317990069310364174568045845059255448763789458223923200000000000000000000000 false
private noncomputable def ibox67 : Fin 4 → FixedTape.I := splitI ibox66 0 29251095333588002776950242472555476366615303334030006583256501872598330918624577894481920000000 false
private noncomputable def ibox68 : Fin 4 → FixedTape.I := splitI ibox66 0 29251095333588002776950242472555476366615303334030006583256501872598330918624577894481920000000 true
private noncomputable def ibox69 : Fin 4 → FixedTape.I := splitI ibox65 2 1887167440876645470317990069310364174568045845059255448763789458223923200000000000000000000000 true
private noncomputable def ibox70 : Fin 4 → FixedTape.I := splitI ibox38 2 2516223254502193960423986759080485566090727793412340598351719277631897600000000000000000000000 true
private noncomputable def ibox71 : Fin 4 → FixedTape.I := splitI ibox70 2 3774334881753290940635980138620728349136091690118510897527578916447846400000000000000000000000 false
private noncomputable def ibox72 : Fin 4 → FixedTape.I := splitI ibox71 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 false
private noncomputable def ibox73 : Fin 4 → FixedTape.I := splitI ibox71 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 true
private noncomputable def ibox74 : Fin 4 → FixedTape.I := splitI ibox70 2 3774334881753290940635980138620728349136091690118510897527578916447846400000000000000000000000 true
private noncomputable def ibox75 : Fin 4 → FixedTape.I := splitI ibox74 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 false
private noncomputable def ibox76 : Fin 4 → FixedTape.I := splitI ibox74 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 true
private noncomputable def ibox77 : Fin 4 → FixedTape.I := splitI ibox33 2 5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 true
private noncomputable def ibox78 : Fin 4 → FixedTape.I := splitI ibox77 1 35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 false
private noncomputable def ibox79 : Fin 4 → FixedTape.I := splitI ibox78 1 32710902308528521485511827868046312359179461314360427778572350609214668800000000000000000000000 false
private noncomputable def ibox80 : Fin 4 → FixedTape.I := splitI ibox78 1 32710902308528521485511827868046312359179461314360427778572350609214668800000000000000000000000 true
private noncomputable def ibox81 : Fin 4 → FixedTape.I := splitI ibox80 2 7548669763506581881271960277241456698272183380237021795055157832895692800000000000000000000000 false
private noncomputable def ibox82 : Fin 4 → FixedTape.I := splitI ibox80 2 7548669763506581881271960277241456698272183380237021795055157832895692800000000000000000000000 true
private noncomputable def ibox83 : Fin 4 → FixedTape.I := splitI ibox77 1 35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 true
private noncomputable def ibox84 : Fin 4 → FixedTape.I := splitI ibox83 1 37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 false
private noncomputable def ibox85 : Fin 4 → FixedTape.I := splitI ibox84 2 7548669763506581881271960277241456698272183380237021795055157832895692800000000000000000000000 false
private noncomputable def ibox86 : Fin 4 → FixedTape.I := faceI ibox85 1 true
private noncomputable def ibox87 : Fin 4 → FixedTape.I := splitI ibox84 2 7548669763506581881271960277241456698272183380237021795055157832895692800000000000000000000000 true
private noncomputable def ibox88 : Fin 4 → FixedTape.I := splitI ibox87 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 false
private noncomputable def ibox89 : Fin 4 → FixedTape.I := splitI ibox87 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 true
private noncomputable def ibox90 : Fin 4 → FixedTape.I := splitI ibox83 1 37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 true
private noncomputable def ibox91 : Fin 4 → FixedTape.I := splitI ibox90 2 7548669763506581881271960277241456698272183380237021795055157832895692800000000000000000000000 false
private noncomputable def ibox92 : Fin 4 → FixedTape.I := splitI ibox91 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 false
private noncomputable def ibox93 : Fin 4 → FixedTape.I := faceI ibox92 1 true
private noncomputable def ibox94 : Fin 4 → FixedTape.I := splitI ibox91 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 true
private noncomputable def ibox95 : Fin 4 → FixedTape.I := faceI ibox94 1 true
private noncomputable def ibox96 : Fin 4 → FixedTape.I := splitI ibox90 2 7548669763506581881271960277241456698272183380237021795055157832895692800000000000000000000000 true
private noncomputable def ibox97 : Fin 4 → FixedTape.I := splitI ibox96 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 false
private noncomputable def ibox98 : Fin 4 → FixedTape.I := faceI ibox97 1 true
private noncomputable def ibox99 : Fin 4 → FixedTape.I := splitI ibox96 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 true
private noncomputable def ibox100 : Fin 4 → FixedTape.I := faceI ibox99 1 true
private noncomputable def ibox101 : Fin 4 → FixedTape.I := splitI ibox22 2 10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 true
private noncomputable def ibox102 : Fin 4 → FixedTape.I := splitI ibox101 1 30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 false
private noncomputable def ibox103 : Fin 4 → FixedTape.I := splitI ibox102 2 15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 false
private noncomputable def ibox104 : Fin 4 → FixedTape.I := splitI ibox103 1 25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 false
private noncomputable def ibox105 : Fin 4 → FixedTape.I := splitI ibox103 1 25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 true
private noncomputable def ibox106 : Fin 4 → FixedTape.I := splitI ibox105 2 12581116272510969802119933795402427830453638967061702991758596388159488000000000000000000000000 false
private noncomputable def ibox107 : Fin 4 → FixedTape.I := splitI ibox105 2 12581116272510969802119933795402427830453638967061702991758596388159488000000000000000000000000 true
private noncomputable def ibox108 : Fin 4 → FixedTape.I := splitI ibox102 2 15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 true
private noncomputable def ibox109 : Fin 4 → FixedTape.I := splitI ibox108 1 25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 false
private noncomputable def ibox110 : Fin 4 → FixedTape.I := splitI ibox108 1 25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 true
private noncomputable def ibox111 : Fin 4 → FixedTape.I := splitI ibox110 2 17613562781515357722967907313563398962635094553886384188462034943423283200000000000000000000000 false
private noncomputable def ibox112 : Fin 4 → FixedTape.I := splitI ibox110 2 17613562781515357722967907313563398962635094553886384188462034943423283200000000000000000000000 true
private noncomputable def ibox113 : Fin 4 → FixedTape.I := splitI ibox101 1 30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 true
private noncomputable def ibox114 : Fin 4 → FixedTape.I := splitI ibox113 2 15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 false
private noncomputable def ibox115 : Fin 4 → FixedTape.I := splitI ibox114 1 35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 false
private noncomputable def ibox116 : Fin 4 → FixedTape.I := splitI ibox115 2 12581116272510969802119933795402427830453638967061702991758596388159488000000000000000000000000 false
private noncomputable def ibox117 : Fin 4 → FixedTape.I := splitI ibox116 1 32710902308528521485511827868046312359179461314360427778572350609214668800000000000000000000000 false
private noncomputable def ibox118 : Fin 4 → FixedTape.I := splitI ibox116 1 32710902308528521485511827868046312359179461314360427778572350609214668800000000000000000000000 true
private noncomputable def ibox119 : Fin 4 → FixedTape.I := splitI ibox115 2 12581116272510969802119933795402427830453638967061702991758596388159488000000000000000000000000 true
private noncomputable def ibox120 : Fin 4 → FixedTape.I := splitI ibox114 1 35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 true
private noncomputable def ibox121 : Fin 4 → FixedTape.I := splitI ibox120 2 12581116272510969802119933795402427830453638967061702991758596388159488000000000000000000000000 false
private noncomputable def ibox122 : Fin 4 → FixedTape.I := splitI ibox121 1 37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 false
private noncomputable def ibox123 : Fin 4 → FixedTape.I := splitI ibox121 1 37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 true
private noncomputable def ibox124 : Fin 4 → FixedTape.I := splitI ibox123 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 false
private noncomputable def ibox125 : Fin 4 → FixedTape.I := splitI ibox123 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 true
private noncomputable def ibox126 : Fin 4 → FixedTape.I := splitI ibox120 2 12581116272510969802119933795402427830453638967061702991758596388159488000000000000000000000000 true
private noncomputable def ibox127 : Fin 4 → FixedTape.I := splitI ibox126 1 37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 false
private noncomputable def ibox128 : Fin 4 → FixedTape.I := splitI ibox126 1 37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 true
private noncomputable def ibox129 : Fin 4 → FixedTape.I := splitI ibox128 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 false
private noncomputable def ibox130 : Fin 4 → FixedTape.I := splitI ibox128 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 true
private noncomputable def ibox131 : Fin 4 → FixedTape.I := splitI ibox113 2 15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 true
private noncomputable def ibox132 : Fin 4 → FixedTape.I := splitI ibox131 1 35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 false
private noncomputable def ibox133 : Fin 4 → FixedTape.I := splitI ibox132 2 17613562781515357722967907313563398962635094553886384188462034943423283200000000000000000000000 false
private noncomputable def ibox134 : Fin 4 → FixedTape.I := splitI ibox132 2 17613562781515357722967907313563398962635094553886384188462034943423283200000000000000000000000 true
private noncomputable def ibox135 : Fin 4 → FixedTape.I := splitI ibox131 1 35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 true
private noncomputable def ibox136 : Fin 4 → FixedTape.I := splitI ibox135 2 17613562781515357722967907313563398962635094553886384188462034943423283200000000000000000000000 false
private noncomputable def ibox137 : Fin 4 → FixedTape.I := splitI ibox136 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 false
private noncomputable def ibox138 : Fin 4 → FixedTape.I := splitI ibox136 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 true
private noncomputable def ibox139 : Fin 4 → FixedTape.I := splitI ibox135 2 17613562781515357722967907313563398962635094553886384188462034943423283200000000000000000000000 true
private noncomputable def ibox140 : Fin 4 → FixedTape.I := splitI ibox139 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 false
private noncomputable def ibox141 : Fin 4 → FixedTape.I := splitI ibox139 0 29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 true
private noncomputable def ibox142 : Fin 4 → FixedTape.I := splitI ibox1 2 20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 true
private noncomputable def ibox143 : Fin 4 → FixedTape.I := splitI ibox142 2 30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 false
private noncomputable def ibox144 : Fin 4 → FixedTape.I := splitI ibox143 1 20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 false
private noncomputable def ibox145 : Fin 4 → FixedTape.I := splitI ibox144 2 25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 false
private noncomputable def ibox146 : Fin 4 → FixedTape.I := splitI ibox145 1 10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 false
private noncomputable def ibox147 : Fin 4 → FixedTape.I := splitI ibox146 2 22646009290519745643815880831724370094816550140711065385165473498687078400000000000000000000000 false
private noncomputable def ibox148 : Fin 4 → FixedTape.I := splitI ibox146 2 22646009290519745643815880831724370094816550140711065385165473498687078400000000000000000000000 true
private noncomputable def ibox149 : Fin 4 → FixedTape.I := splitI ibox148 1 5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 false
private noncomputable def ibox150 : Fin 4 → FixedTape.I := splitI ibox148 1 5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 true
private noncomputable def ibox151 : Fin 4 → FixedTape.I := splitI ibox145 1 10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 true
private noncomputable def ibox152 : Fin 4 → FixedTape.I := splitI ibox151 2 22646009290519745643815880831724370094816550140711065385165473498687078400000000000000000000000 false
private noncomputable def ibox153 : Fin 4 → FixedTape.I := splitI ibox151 2 22646009290519745643815880831724370094816550140711065385165473498687078400000000000000000000000 true
private noncomputable def ibox154 : Fin 4 → FixedTape.I := splitI ibox153 1 15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 false
private noncomputable def ibox155 : Fin 4 → FixedTape.I := splitI ibox153 1 15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 true
private noncomputable def ibox156 : Fin 4 → FixedTape.I := splitI ibox144 2 25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 true
private noncomputable def ibox157 : Fin 4 → FixedTape.I := splitI ibox156 2 27678455799524133564663854349885341226998005727535746581868912053950873600000000000000000000000 false
private noncomputable def ibox158 : Fin 4 → FixedTape.I := splitI ibox157 1 10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 false
private noncomputable def ibox159 : Fin 4 → FixedTape.I := splitI ibox158 1 5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 false
private noncomputable def ibox160 : Fin 4 → FixedTape.I := splitI ibox158 1 5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 true
private noncomputable def ibox161 : Fin 4 → FixedTape.I := splitI ibox157 1 10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 true
private noncomputable def ibox162 : Fin 4 → FixedTape.I := splitI ibox161 2 26420344172273036584451860970345098443952641830829576282693052415134924800000000000000000000000 false
private noncomputable def ibox163 : Fin 4 → FixedTape.I := splitI ibox161 2 26420344172273036584451860970345098443952641830829576282693052415134924800000000000000000000000 true
private noncomputable def ibox164 : Fin 4 → FixedTape.I := splitI ibox156 2 27678455799524133564663854349885341226998005727535746581868912053950873600000000000000000000000 true
private noncomputable def ibox165 : Fin 4 → FixedTape.I := splitI ibox164 1 10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 false
private noncomputable def ibox166 : Fin 4 → FixedTape.I := splitI ibox165 2 28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000 false
private noncomputable def ibox167 : Fin 4 → FixedTape.I := splitI ibox165 2 28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000 true
private noncomputable def ibox168 : Fin 4 → FixedTape.I := splitI ibox164 1 10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 true
private noncomputable def ibox169 : Fin 4 → FixedTape.I := splitI ibox168 2 28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000 false
private noncomputable def ibox170 : Fin 4 → FixedTape.I := splitI ibox168 2 28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000 true
private noncomputable def ibox171 : Fin 4 → FixedTape.I := splitI ibox143 1 20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 true
private noncomputable def ibox172 : Fin 4 → FixedTape.I := splitI ibox171 2 25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 false
private noncomputable def ibox173 : Fin 4 → FixedTape.I := splitI ibox172 1 30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 false
private noncomputable def ibox174 : Fin 4 → FixedTape.I := splitI ibox173 2 22646009290519745643815880831724370094816550140711065385165473498687078400000000000000000000000 false
private noncomputable def ibox175 : Fin 4 → FixedTape.I := splitI ibox174 1 25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 false
private noncomputable def ibox176 : Fin 4 → FixedTape.I := splitI ibox174 1 25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 true
private noncomputable def ibox177 : Fin 4 → FixedTape.I := splitI ibox173 2 22646009290519745643815880831724370094816550140711065385165473498687078400000000000000000000000 true
private noncomputable def ibox178 : Fin 4 → FixedTape.I := splitI ibox177 1 25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 false
private noncomputable def ibox179 : Fin 4 → FixedTape.I := splitI ibox177 1 25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 true
private noncomputable def ibox180 : Fin 4 → FixedTape.I := splitI ibox172 1 30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 true
private noncomputable def ibox181 : Fin 4 → FixedTape.I := splitI ibox180 2 22646009290519745643815880831724370094816550140711065385165473498687078400000000000000000000000 false
private noncomputable def ibox182 : Fin 4 → FixedTape.I := splitI ibox181 1 35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 false
private noncomputable def ibox183 : Fin 4 → FixedTape.I := splitI ibox181 1 35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 true
private noncomputable def ibox184 : Fin 4 → FixedTape.I := splitI ibox180 2 22646009290519745643815880831724370094816550140711065385165473498687078400000000000000000000000 true
private noncomputable def ibox185 : Fin 4 → FixedTape.I := splitI ibox184 1 35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 false
private noncomputable def ibox186 : Fin 4 → FixedTape.I := splitI ibox184 1 35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 true
private noncomputable def ibox187 : Fin 4 → FixedTape.I := splitI ibox171 2 25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 true
private noncomputable def ibox188 : Fin 4 → FixedTape.I := splitI ibox187 2 27678455799524133564663854349885341226998005727535746581868912053950873600000000000000000000000 false
private noncomputable def ibox189 : Fin 4 → FixedTape.I := splitI ibox188 1 30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 false
private noncomputable def ibox190 : Fin 4 → FixedTape.I := splitI ibox189 2 26420344172273036584451860970345098443952641830829576282693052415134924800000000000000000000000 false
private noncomputable def ibox191 : Fin 4 → FixedTape.I := splitI ibox189 2 26420344172273036584451860970345098443952641830829576282693052415134924800000000000000000000000 true
private noncomputable def ibox192 : Fin 4 → FixedTape.I := splitI ibox188 1 30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 true
private noncomputable def ibox193 : Fin 4 → FixedTape.I := splitI ibox192 1 35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 false
private noncomputable def ibox194 : Fin 4 → FixedTape.I := splitI ibox192 1 35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 true
private noncomputable def ibox195 : Fin 4 → FixedTape.I := splitI ibox187 2 27678455799524133564663854349885341226998005727535746581868912053950873600000000000000000000000 true
private noncomputable def ibox196 : Fin 4 → FixedTape.I := splitI ibox195 1 30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 false
private noncomputable def ibox197 : Fin 4 → FixedTape.I := splitI ibox196 2 28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000 false
private noncomputable def ibox198 : Fin 4 → FixedTape.I := splitI ibox196 2 28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000 true
private noncomputable def ibox199 : Fin 4 → FixedTape.I := splitI ibox195 1 30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 true
private noncomputable def ibox200 : Fin 4 → FixedTape.I := splitI ibox199 2 28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000 false
private noncomputable def ibox201 : Fin 4 → FixedTape.I := splitI ibox199 2 28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000 true
private noncomputable def ibox202 : Fin 4 → FixedTape.I := splitI ibox142 2 30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 true
private noncomputable def ibox203 : Fin 4 → FixedTape.I := splitI ibox202 2 35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 false
private noncomputable def ibox204 : Fin 4 → FixedTape.I := splitI ibox203 1 20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 false
private noncomputable def ibox205 : Fin 4 → FixedTape.I := splitI ibox204 2 32710902308528521485511827868046312359179461314360427778572350609214668800000000000000000000000 false
private noncomputable def ibox206 : Fin 4 → FixedTape.I := splitI ibox205 1 10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 false
private noncomputable def ibox207 : Fin 4 → FixedTape.I := splitI ibox206 2 31452790681277424505299834488506069576134097417654257479396490970398720000000000000000000000000 false
private noncomputable def ibox208 : Fin 4 → FixedTape.I := splitI ibox206 2 31452790681277424505299834488506069576134097417654257479396490970398720000000000000000000000000 true
private noncomputable def ibox209 : Fin 4 → FixedTape.I := splitI ibox205 1 10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 true
private noncomputable def ibox210 : Fin 4 → FixedTape.I := splitI ibox209 2 31452790681277424505299834488506069576134097417654257479396490970398720000000000000000000000000 false
private noncomputable def ibox211 : Fin 4 → FixedTape.I := splitI ibox209 2 31452790681277424505299834488506069576134097417654257479396490970398720000000000000000000000000 true
private noncomputable def ibox212 : Fin 4 → FixedTape.I := splitI ibox204 2 32710902308528521485511827868046312359179461314360427778572350609214668800000000000000000000000 true
private noncomputable def ibox213 : Fin 4 → FixedTape.I := splitI ibox212 2 33969013935779618465723821247586555142224825211066598077748210248030617600000000000000000000000 false
private noncomputable def ibox214 : Fin 4 → FixedTape.I := splitI ibox212 2 33969013935779618465723821247586555142224825211066598077748210248030617600000000000000000000000 true
private noncomputable def ibox215 : Fin 4 → FixedTape.I := splitI ibox203 1 20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 true
private noncomputable def ibox216 : Fin 4 → FixedTape.I := splitI ibox215 2 32710902308528521485511827868046312359179461314360427778572350609214668800000000000000000000000 false
private noncomputable def ibox217 : Fin 4 → FixedTape.I := splitI ibox216 1 30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 false
private noncomputable def ibox218 : Fin 4 → FixedTape.I := splitI ibox217 2 31452790681277424505299834488506069576134097417654257479396490970398720000000000000000000000000 false
private noncomputable def ibox219 : Fin 4 → FixedTape.I := splitI ibox217 2 31452790681277424505299834488506069576134097417654257479396490970398720000000000000000000000000 true
private noncomputable def ibox220 : Fin 4 → FixedTape.I := splitI ibox216 1 30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 true
private noncomputable def ibox221 : Fin 4 → FixedTape.I := faceI ibox220 2 false
private noncomputable def ibox222 : Fin 4 → FixedTape.I := splitI ibox215 2 32710902308528521485511827868046312359179461314360427778572350609214668800000000000000000000000 true
private noncomputable def ibox223 : Fin 4 → FixedTape.I := faceI ibox222 2 false
private noncomputable def ibox224 : Fin 4 → FixedTape.I := splitI ibox223 1 30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 false
private noncomputable def ibox225 : Fin 4 → FixedTape.I := splitI ibox223 1 30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 true
private noncomputable def ibox226 : Fin 4 → FixedTape.I := splitI ibox202 2 35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 true
private noncomputable def ibox227 : Fin 4 → FixedTape.I := splitI ibox226 1 20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 false
private noncomputable def ibox228 : Fin 4 → FixedTape.I := splitI ibox227 2 37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 false
private noncomputable def ibox229 : Fin 4 → FixedTape.I := faceI ibox228 2 false
private noncomputable def ibox230 : Fin 4 → FixedTape.I := splitI ibox227 2 37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 true
private noncomputable def ibox231 : Fin 4 → FixedTape.I := splitI ibox226 1 20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 true
private noncomputable def ibox232 : Fin 4 → FixedTape.I := splitI ibox231 2 37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 false
private noncomputable def ibox233 : Fin 4 → FixedTape.I := faceI ibox232 2 false
private noncomputable def ibox234 : Fin 4 → FixedTape.I := splitI ibox231 2 37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 true
private noncomputable def ibox235 : Fin 4 → FixedTape.I := faceI ibox234 2 false
private noncomputable def tree235 : TapeTree := .centered (candidateRows ibox235) (candidateRows (FixedTape.midBox ibox235))
attribute [irreducible] tree235
private theorem sign_235 : 2*denominator*(computed denominator (FixedTape.midBox ibox235)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox235).gradient k).lo.natAbs ((computed denominator ibox235).gradient k).hi.natAbs : Int)*((ibox235 k).hi-(ibox235 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox235
    (computed denominator ibox235) (computed denominator (FixedTape.midBox ibox235))
    (by decide +kernel)
private theorem midpoint_even_235 : ∀ k, 2 ∣ (ibox235 k).lo+(ibox235 k).hi := by decide +kernel
private theorem accepted_235 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox235) tree235 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox235 midpoint_even_235
  simp only [tree235,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox235,candidate_valid h (FixedTape.midBox ibox235),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox235 113 (FixedTape.rowsAux denominator ibox235 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox235) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_235
private noncomputable def tree234 : TapeTree := .face 2 false (candidateRows ibox234) tree235
attribute [irreducible] tree234
private theorem sign_234 : ((computed denominator ibox234).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_234 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox234) tree234 = true := by
  simp only [tree234,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox234,?_,accepted_235 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox234)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox234).gradient 2).hi) denominator_positive).1 sign_234
private noncomputable def tree233 : TapeTree := .centered (candidateRows ibox233) (candidateRows (FixedTape.midBox ibox233))
attribute [irreducible] tree233
private theorem sign_233 : 2*denominator*(computed denominator (FixedTape.midBox ibox233)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox233).gradient k).lo.natAbs ((computed denominator ibox233).gradient k).hi.natAbs : Int)*((ibox233 k).hi-(ibox233 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox233
    (computed denominator ibox233) (computed denominator (FixedTape.midBox ibox233))
    (by decide +kernel)
private theorem midpoint_even_233 : ∀ k, 2 ∣ (ibox233 k).lo+(ibox233 k).hi := by decide +kernel
private theorem accepted_233 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox233) tree233 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox233 midpoint_even_233
  simp only [tree233,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox233,candidate_valid h (FixedTape.midBox ibox233),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox233 113 (FixedTape.rowsAux denominator ibox233 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox233) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_233
private noncomputable def tree232 : TapeTree := .face 2 false (candidateRows ibox232) tree233
attribute [irreducible] tree232
private theorem sign_232 : ((computed denominator ibox232).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_232 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox232) tree232 = true := by
  simp only [tree232,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox232,?_,accepted_233 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox232)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox232).gradient 2).hi) denominator_positive).1 sign_232
private noncomputable def tree231 : TapeTree := .split 2 (((37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree232 tree234
attribute [irreducible] tree231
private theorem accepted_231 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox231) tree231 = true := by
  simp only [tree231,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox231 2 (37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 : Int) false,decode_split denominator ibox231 2 (37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_232 h,accepted_234 h⟩
private noncomputable def tree230 : TapeTree := .centered (candidateRows ibox230) (candidateRows (FixedTape.midBox ibox230))
attribute [irreducible] tree230
private theorem sign_230 : 2*denominator*(computed denominator (FixedTape.midBox ibox230)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox230).gradient k).lo.natAbs ((computed denominator ibox230).gradient k).hi.natAbs : Int)*((ibox230 k).hi-(ibox230 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox230
    (computed denominator ibox230) (computed denominator (FixedTape.midBox ibox230))
    (by decide +kernel)
private theorem midpoint_even_230 : ∀ k, 2 ∣ (ibox230 k).lo+(ibox230 k).hi := by decide +kernel
private theorem accepted_230 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox230) tree230 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox230 midpoint_even_230
  simp only [tree230,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox230,candidate_valid h (FixedTape.midBox ibox230),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox230 113 (FixedTape.rowsAux denominator ibox230 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox230) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_230
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
private noncomputable def tree228 : TapeTree := .face 2 false (candidateRows ibox228) tree229
attribute [irreducible] tree228
private theorem sign_228 : ((computed denominator ibox228).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_228 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox228) tree228 = true := by
  simp only [tree228,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox228,?_,accepted_229 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox228)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox228).gradient 2).hi) denominator_positive).1 sign_228
private noncomputable def tree227 : TapeTree := .split 2 (((37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree228 tree230
attribute [irreducible] tree227
private theorem accepted_227 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox227) tree227 = true := by
  simp only [tree227,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox227 2 (37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 : Int) false,decode_split denominator ibox227 2 (37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_228 h,accepted_230 h⟩
private noncomputable def tree226 : TapeTree := .split 1 (((20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree227 tree231
attribute [irreducible] tree226
private theorem accepted_226 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox226) tree226 = true := by
  simp only [tree226,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox226 1 (20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 : Int) false,decode_split denominator ibox226 1 (20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_227 h,accepted_231 h⟩
private noncomputable def tree225 : TapeTree := .centered (candidateRows ibox225) (candidateRows (FixedTape.midBox ibox225))
attribute [irreducible] tree225
private theorem sign_225 : 2*denominator*(computed denominator (FixedTape.midBox ibox225)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox225).gradient k).lo.natAbs ((computed denominator ibox225).gradient k).hi.natAbs : Int)*((ibox225 k).hi-(ibox225 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox225
    (computed denominator ibox225) (computed denominator (FixedTape.midBox ibox225))
    (by decide +kernel)
private theorem midpoint_even_225 : ∀ k, 2 ∣ (ibox225 k).lo+(ibox225 k).hi := by decide +kernel
private theorem accepted_225 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox225) tree225 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox225 midpoint_even_225
  simp only [tree225,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox225,candidate_valid h (FixedTape.midBox ibox225),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox225 113 (FixedTape.rowsAux denominator ibox225 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox225) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_225
private noncomputable def tree224 : TapeTree := .centered (candidateRows ibox224) (candidateRows (FixedTape.midBox ibox224))
attribute [irreducible] tree224
private theorem sign_224 : 2*denominator*(computed denominator (FixedTape.midBox ibox224)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox224).gradient k).lo.natAbs ((computed denominator ibox224).gradient k).hi.natAbs : Int)*((ibox224 k).hi-(ibox224 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox224
    (computed denominator ibox224) (computed denominator (FixedTape.midBox ibox224))
    (by decide +kernel)
private theorem midpoint_even_224 : ∀ k, 2 ∣ (ibox224 k).lo+(ibox224 k).hi := by decide +kernel
private theorem accepted_224 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox224) tree224 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox224 midpoint_even_224
  simp only [tree224,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox224,candidate_valid h (FixedTape.midBox ibox224),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox224 113 (FixedTape.rowsAux denominator ibox224 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox224) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_224
private noncomputable def tree223 : TapeTree := .split 1 (((30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree224 tree225
attribute [irreducible] tree223
private theorem accepted_223 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox223) tree223 = true := by
  simp only [tree223,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox223 1 (30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) false,decode_split denominator ibox223 1 (30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_224 h,accepted_225 h⟩
private noncomputable def tree222 : TapeTree := .face 2 false (candidateRows ibox222) tree223
attribute [irreducible] tree222
private theorem sign_222 : ((computed denominator ibox222).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_222 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox222) tree222 = true := by
  simp only [tree222,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox222,?_,accepted_223 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox222)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox222).gradient 2).hi) denominator_positive).1 sign_222
private noncomputable def tree221 : TapeTree := .centered (candidateRows ibox221) (candidateRows (FixedTape.midBox ibox221))
attribute [irreducible] tree221
private theorem sign_221 : 2*denominator*(computed denominator (FixedTape.midBox ibox221)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox221).gradient k).lo.natAbs ((computed denominator ibox221).gradient k).hi.natAbs : Int)*((ibox221 k).hi-(ibox221 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox221
    (computed denominator ibox221) (computed denominator (FixedTape.midBox ibox221))
    (by decide +kernel)
private theorem midpoint_even_221 : ∀ k, 2 ∣ (ibox221 k).lo+(ibox221 k).hi := by decide +kernel
private theorem accepted_221 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox221) tree221 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox221 midpoint_even_221
  simp only [tree221,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox221,candidate_valid h (FixedTape.midBox ibox221),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox221 113 (FixedTape.rowsAux denominator ibox221 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox221) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_221
private noncomputable def tree220 : TapeTree := .face 2 false (candidateRows ibox220) tree221
attribute [irreducible] tree220
private theorem sign_220 : ((computed denominator ibox220).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_220 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox220) tree220 = true := by
  simp only [tree220,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox220,?_,accepted_221 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox220)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox220).gradient 2).hi) denominator_positive).1 sign_220
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
private noncomputable def tree218 : TapeTree := .centered (candidateRows ibox218) (candidateRows (FixedTape.midBox ibox218))
attribute [irreducible] tree218
private theorem sign_218 : 2*denominator*(computed denominator (FixedTape.midBox ibox218)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox218).gradient k).lo.natAbs ((computed denominator ibox218).gradient k).hi.natAbs : Int)*((ibox218 k).hi-(ibox218 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox218
    (computed denominator ibox218) (computed denominator (FixedTape.midBox ibox218))
    (by decide +kernel)
private theorem midpoint_even_218 : ∀ k, 2 ∣ (ibox218 k).lo+(ibox218 k).hi := by decide +kernel
private theorem accepted_218 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox218) tree218 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox218 midpoint_even_218
  simp only [tree218,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox218,candidate_valid h (FixedTape.midBox ibox218),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox218 113 (FixedTape.rowsAux denominator ibox218 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox218) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_218
private noncomputable def tree217 : TapeTree := .split 2 (((31452790681277424505299834488506069576134097417654257479396490970398720000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree218 tree219
attribute [irreducible] tree217
private theorem accepted_217 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox217) tree217 = true := by
  simp only [tree217,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox217 2 (31452790681277424505299834488506069576134097417654257479396490970398720000000000000000000000000 : Int) false,decode_split denominator ibox217 2 (31452790681277424505299834488506069576134097417654257479396490970398720000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_218 h,accepted_219 h⟩
private noncomputable def tree216 : TapeTree := .split 1 (((30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree217 tree220
attribute [irreducible] tree216
private theorem accepted_216 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox216) tree216 = true := by
  simp only [tree216,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox216 1 (30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) false,decode_split denominator ibox216 1 (30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_217 h,accepted_220 h⟩
private noncomputable def tree215 : TapeTree := .split 2 (((32710902308528521485511827868046312359179461314360427778572350609214668800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree216 tree222
attribute [irreducible] tree215
private theorem accepted_215 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox215) tree215 = true := by
  simp only [tree215,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox215 2 (32710902308528521485511827868046312359179461314360427778572350609214668800000000000000000000000 : Int) false,decode_split denominator ibox215 2 (32710902308528521485511827868046312359179461314360427778572350609214668800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_216 h,accepted_222 h⟩
private noncomputable def tree214 : TapeTree := .centered (candidateRows ibox214) (candidateRows (FixedTape.midBox ibox214))
attribute [irreducible] tree214
private theorem sign_214 : 2*denominator*(computed denominator (FixedTape.midBox ibox214)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox214).gradient k).lo.natAbs ((computed denominator ibox214).gradient k).hi.natAbs : Int)*((ibox214 k).hi-(ibox214 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox214
    (computed denominator ibox214) (computed denominator (FixedTape.midBox ibox214))
    (by decide +kernel)
private theorem midpoint_even_214 : ∀ k, 2 ∣ (ibox214 k).lo+(ibox214 k).hi := by decide +kernel
private theorem accepted_214 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox214) tree214 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox214 midpoint_even_214
  simp only [tree214,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox214,candidate_valid h (FixedTape.midBox ibox214),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox214 113 (FixedTape.rowsAux denominator ibox214 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox214) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_214
private noncomputable def tree213 : TapeTree := .centered (candidateRows ibox213) (candidateRows (FixedTape.midBox ibox213))
attribute [irreducible] tree213
private theorem sign_213 : 2*denominator*(computed denominator (FixedTape.midBox ibox213)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox213).gradient k).lo.natAbs ((computed denominator ibox213).gradient k).hi.natAbs : Int)*((ibox213 k).hi-(ibox213 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox213
    (computed denominator ibox213) (computed denominator (FixedTape.midBox ibox213))
    (by decide +kernel)
private theorem midpoint_even_213 : ∀ k, 2 ∣ (ibox213 k).lo+(ibox213 k).hi := by decide +kernel
private theorem accepted_213 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox213) tree213 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox213 midpoint_even_213
  simp only [tree213,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox213,candidate_valid h (FixedTape.midBox ibox213),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox213 113 (FixedTape.rowsAux denominator ibox213 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox213) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_213
private noncomputable def tree212 : TapeTree := .split 2 (((33969013935779618465723821247586555142224825211066598077748210248030617600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree213 tree214
attribute [irreducible] tree212
private theorem accepted_212 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox212) tree212 = true := by
  simp only [tree212,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox212 2 (33969013935779618465723821247586555142224825211066598077748210248030617600000000000000000000000 : Int) false,decode_split denominator ibox212 2 (33969013935779618465723821247586555142224825211066598077748210248030617600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_213 h,accepted_214 h⟩
private noncomputable def tree211 : TapeTree := .centered (candidateRows ibox211) (candidateRows (FixedTape.midBox ibox211))
attribute [irreducible] tree211
private theorem sign_211 : 2*denominator*(computed denominator (FixedTape.midBox ibox211)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox211).gradient k).lo.natAbs ((computed denominator ibox211).gradient k).hi.natAbs : Int)*((ibox211 k).hi-(ibox211 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox211
    (computed denominator ibox211) (computed denominator (FixedTape.midBox ibox211))
    (by decide +kernel)
private theorem midpoint_even_211 : ∀ k, 2 ∣ (ibox211 k).lo+(ibox211 k).hi := by decide +kernel
private theorem accepted_211 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox211) tree211 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox211 midpoint_even_211
  simp only [tree211,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox211,candidate_valid h (FixedTape.midBox ibox211),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox211 113 (FixedTape.rowsAux denominator ibox211 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox211) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_211
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
private noncomputable def tree209 : TapeTree := .split 2 (((31452790681277424505299834488506069576134097417654257479396490970398720000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree210 tree211
attribute [irreducible] tree209
private theorem accepted_209 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox209) tree209 = true := by
  simp only [tree209,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox209 2 (31452790681277424505299834488506069576134097417654257479396490970398720000000000000000000000000 : Int) false,decode_split denominator ibox209 2 (31452790681277424505299834488506069576134097417654257479396490970398720000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_210 h,accepted_211 h⟩
private noncomputable def tree208 : TapeTree := .centered (candidateRows ibox208) (candidateRows (FixedTape.midBox ibox208))
attribute [irreducible] tree208
private theorem sign_208 : 2*denominator*(computed denominator (FixedTape.midBox ibox208)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox208).gradient k).lo.natAbs ((computed denominator ibox208).gradient k).hi.natAbs : Int)*((ibox208 k).hi-(ibox208 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox208
    (computed denominator ibox208) (computed denominator (FixedTape.midBox ibox208))
    (by decide +kernel)
private theorem midpoint_even_208 : ∀ k, 2 ∣ (ibox208 k).lo+(ibox208 k).hi := by decide +kernel
private theorem accepted_208 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox208) tree208 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox208 midpoint_even_208
  simp only [tree208,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox208,candidate_valid h (FixedTape.midBox ibox208),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox208 113 (FixedTape.rowsAux denominator ibox208 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox208) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_208
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
private noncomputable def tree206 : TapeTree := .split 2 (((31452790681277424505299834488506069576134097417654257479396490970398720000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree207 tree208
attribute [irreducible] tree206
private theorem accepted_206 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox206) tree206 = true := by
  simp only [tree206,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox206 2 (31452790681277424505299834488506069576134097417654257479396490970398720000000000000000000000000 : Int) false,decode_split denominator ibox206 2 (31452790681277424505299834488506069576134097417654257479396490970398720000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_207 h,accepted_208 h⟩
private noncomputable def tree205 : TapeTree := .split 1 (((10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree206 tree209
attribute [irreducible] tree205
private theorem accepted_205 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox205) tree205 = true := by
  simp only [tree205,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox205 1 (10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) false,decode_split denominator ibox205 1 (10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_206 h,accepted_209 h⟩
private noncomputable def tree204 : TapeTree := .split 2 (((32710902308528521485511827868046312359179461314360427778572350609214668800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree205 tree212
attribute [irreducible] tree204
private theorem accepted_204 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox204) tree204 = true := by
  simp only [tree204,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox204 2 (32710902308528521485511827868046312359179461314360427778572350609214668800000000000000000000000 : Int) false,decode_split denominator ibox204 2 (32710902308528521485511827868046312359179461314360427778572350609214668800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_205 h,accepted_212 h⟩
private noncomputable def tree203 : TapeTree := .split 1 (((20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree204 tree215
attribute [irreducible] tree203
private theorem accepted_203 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox203) tree203 = true := by
  simp only [tree203,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox203 1 (20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 : Int) false,decode_split denominator ibox203 1 (20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_204 h,accepted_215 h⟩
private noncomputable def tree202 : TapeTree := .split 2 (((35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree203 tree226
attribute [irreducible] tree202
private theorem accepted_202 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox202) tree202 = true := by
  simp only [tree202,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox202 2 (35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) false,decode_split denominator ibox202 2 (35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_203 h,accepted_226 h⟩
private noncomputable def tree201 : TapeTree := .centered (candidateRows ibox201) (candidateRows (FixedTape.midBox ibox201))
attribute [irreducible] tree201
private theorem sign_201 : 2*denominator*(computed denominator (FixedTape.midBox ibox201)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox201).gradient k).lo.natAbs ((computed denominator ibox201).gradient k).hi.natAbs : Int)*((ibox201 k).hi-(ibox201 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox201
    (computed denominator ibox201) (computed denominator (FixedTape.midBox ibox201))
    (by decide +kernel)
private theorem midpoint_even_201 : ∀ k, 2 ∣ (ibox201 k).lo+(ibox201 k).hi := by decide +kernel
private theorem accepted_201 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox201) tree201 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox201 midpoint_even_201
  simp only [tree201,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox201,candidate_valid h (FixedTape.midBox ibox201),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox201 113 (FixedTape.rowsAux denominator ibox201 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox201) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_201
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
private noncomputable def tree199 : TapeTree := .split 2 (((28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree200 tree201
attribute [irreducible] tree199
private theorem accepted_199 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox199) tree199 = true := by
  simp only [tree199,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox199 2 (28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000 : Int) false,decode_split denominator ibox199 2 (28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_200 h,accepted_201 h⟩
private noncomputable def tree198 : TapeTree := .centered (candidateRows ibox198) (candidateRows (FixedTape.midBox ibox198))
attribute [irreducible] tree198
private theorem sign_198 : 2*denominator*(computed denominator (FixedTape.midBox ibox198)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox198).gradient k).lo.natAbs ((computed denominator ibox198).gradient k).hi.natAbs : Int)*((ibox198 k).hi-(ibox198 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox198
    (computed denominator ibox198) (computed denominator (FixedTape.midBox ibox198))
    (by decide +kernel)
private theorem midpoint_even_198 : ∀ k, 2 ∣ (ibox198 k).lo+(ibox198 k).hi := by decide +kernel
private theorem accepted_198 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox198) tree198 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox198 midpoint_even_198
  simp only [tree198,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox198,candidate_valid h (FixedTape.midBox ibox198),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox198 113 (FixedTape.rowsAux denominator ibox198 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox198) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_198
private noncomputable def tree197 : TapeTree := .centered (candidateRows ibox197) (candidateRows (FixedTape.midBox ibox197))
attribute [irreducible] tree197
private theorem sign_197 : 2*denominator*(computed denominator (FixedTape.midBox ibox197)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox197).gradient k).lo.natAbs ((computed denominator ibox197).gradient k).hi.natAbs : Int)*((ibox197 k).hi-(ibox197 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox197
    (computed denominator ibox197) (computed denominator (FixedTape.midBox ibox197))
    (by decide +kernel)
private theorem midpoint_even_197 : ∀ k, 2 ∣ (ibox197 k).lo+(ibox197 k).hi := by decide +kernel
private theorem accepted_197 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox197) tree197 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox197 midpoint_even_197
  simp only [tree197,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox197,candidate_valid h (FixedTape.midBox ibox197),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox197 113 (FixedTape.rowsAux denominator ibox197 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox197) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_197
private noncomputable def tree196 : TapeTree := .split 2 (((28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree197 tree198
attribute [irreducible] tree196
private theorem accepted_196 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox196) tree196 = true := by
  simp only [tree196,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox196 2 (28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000 : Int) false,decode_split denominator ibox196 2 (28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_197 h,accepted_198 h⟩
private noncomputable def tree195 : TapeTree := .split 1 (((30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree196 tree199
attribute [irreducible] tree195
private theorem accepted_195 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox195) tree195 = true := by
  simp only [tree195,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox195 1 (30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) false,decode_split denominator ibox195 1 (30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_196 h,accepted_199 h⟩
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
private noncomputable def tree193 : TapeTree := .centered (candidateRows ibox193) (candidateRows (FixedTape.midBox ibox193))
attribute [irreducible] tree193
private theorem sign_193 : 2*denominator*(computed denominator (FixedTape.midBox ibox193)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox193).gradient k).lo.natAbs ((computed denominator ibox193).gradient k).hi.natAbs : Int)*((ibox193 k).hi-(ibox193 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox193
    (computed denominator ibox193) (computed denominator (FixedTape.midBox ibox193))
    (by decide +kernel)
private theorem midpoint_even_193 : ∀ k, 2 ∣ (ibox193 k).lo+(ibox193 k).hi := by decide +kernel
private theorem accepted_193 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox193) tree193 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox193 midpoint_even_193
  simp only [tree193,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox193,candidate_valid h (FixedTape.midBox ibox193),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox193 113 (FixedTape.rowsAux denominator ibox193 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox193) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_193
private noncomputable def tree192 : TapeTree := .split 1 (((35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree193 tree194
attribute [irreducible] tree192
private theorem accepted_192 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox192) tree192 = true := by
  simp only [tree192,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox192 1 (35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) false,decode_split denominator ibox192 1 (35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_193 h,accepted_194 h⟩
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
private noncomputable def tree190 : TapeTree := .centered (candidateRows ibox190) (candidateRows (FixedTape.midBox ibox190))
attribute [irreducible] tree190
private theorem sign_190 : 2*denominator*(computed denominator (FixedTape.midBox ibox190)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox190).gradient k).lo.natAbs ((computed denominator ibox190).gradient k).hi.natAbs : Int)*((ibox190 k).hi-(ibox190 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox190
    (computed denominator ibox190) (computed denominator (FixedTape.midBox ibox190))
    (by decide +kernel)
private theorem midpoint_even_190 : ∀ k, 2 ∣ (ibox190 k).lo+(ibox190 k).hi := by decide +kernel
private theorem accepted_190 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox190) tree190 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox190 midpoint_even_190
  simp only [tree190,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox190,candidate_valid h (FixedTape.midBox ibox190),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox190 113 (FixedTape.rowsAux denominator ibox190 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox190) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_190
private noncomputable def tree189 : TapeTree := .split 2 (((26420344172273036584451860970345098443952641830829576282693052415134924800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree190 tree191
attribute [irreducible] tree189
private theorem accepted_189 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox189) tree189 = true := by
  simp only [tree189,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox189 2 (26420344172273036584451860970345098443952641830829576282693052415134924800000000000000000000000 : Int) false,decode_split denominator ibox189 2 (26420344172273036584451860970345098443952641830829576282693052415134924800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_190 h,accepted_191 h⟩
private noncomputable def tree188 : TapeTree := .split 1 (((30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree189 tree192
attribute [irreducible] tree188
private theorem accepted_188 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox188) tree188 = true := by
  simp only [tree188,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox188 1 (30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) false,decode_split denominator ibox188 1 (30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_189 h,accepted_192 h⟩
private noncomputable def tree187 : TapeTree := .split 2 (((27678455799524133564663854349885341226998005727535746581868912053950873600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree188 tree195
attribute [irreducible] tree187
private theorem accepted_187 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox187) tree187 = true := by
  simp only [tree187,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox187 2 (27678455799524133564663854349885341226998005727535746581868912053950873600000000000000000000000 : Int) false,decode_split denominator ibox187 2 (27678455799524133564663854349885341226998005727535746581868912053950873600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_188 h,accepted_195 h⟩
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
private noncomputable def tree184 : TapeTree := .split 1 (((35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree185 tree186
attribute [irreducible] tree184
private theorem accepted_184 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox184) tree184 = true := by
  simp only [tree184,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox184 1 (35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) false,decode_split denominator ibox184 1 (35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) true]
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
private noncomputable def tree181 : TapeTree := .split 1 (((35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree182 tree183
attribute [irreducible] tree181
private theorem accepted_181 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox181) tree181 = true := by
  simp only [tree181,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox181 1 (35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) false,decode_split denominator ibox181 1 (35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_182 h,accepted_183 h⟩
private noncomputable def tree180 : TapeTree := .split 2 (((22646009290519745643815880831724370094816550140711065385165473498687078400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree181 tree184
attribute [irreducible] tree180
private theorem accepted_180 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox180) tree180 = true := by
  simp only [tree180,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox180 2 (22646009290519745643815880831724370094816550140711065385165473498687078400000000000000000000000 : Int) false,decode_split denominator ibox180 2 (22646009290519745643815880831724370094816550140711065385165473498687078400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_181 h,accepted_184 h⟩
private noncomputable def tree179 : TapeTree := .centered (candidateRows ibox179) (candidateRows (FixedTape.midBox ibox179))
attribute [irreducible] tree179
private theorem sign_179 : 2*denominator*(computed denominator (FixedTape.midBox ibox179)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox179).gradient k).lo.natAbs ((computed denominator ibox179).gradient k).hi.natAbs : Int)*((ibox179 k).hi-(ibox179 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox179
    (computed denominator ibox179) (computed denominator (FixedTape.midBox ibox179))
    (by decide +kernel)
private theorem midpoint_even_179 : ∀ k, 2 ∣ (ibox179 k).lo+(ibox179 k).hi := by decide +kernel
private theorem accepted_179 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox179) tree179 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox179 midpoint_even_179
  simp only [tree179,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox179,candidate_valid h (FixedTape.midBox ibox179),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox179 113 (FixedTape.rowsAux denominator ibox179 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox179) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_179
private noncomputable def tree178 : TapeTree := .centered (candidateRows ibox178) (candidateRows (FixedTape.midBox ibox178))
attribute [irreducible] tree178
private theorem sign_178 : 2*denominator*(computed denominator (FixedTape.midBox ibox178)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox178).gradient k).lo.natAbs ((computed denominator ibox178).gradient k).hi.natAbs : Int)*((ibox178 k).hi-(ibox178 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox178
    (computed denominator ibox178) (computed denominator (FixedTape.midBox ibox178))
    (by decide +kernel)
private theorem midpoint_even_178 : ∀ k, 2 ∣ (ibox178 k).lo+(ibox178 k).hi := by decide +kernel
private theorem accepted_178 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox178) tree178 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox178 midpoint_even_178
  simp only [tree178,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox178,candidate_valid h (FixedTape.midBox ibox178),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox178 113 (FixedTape.rowsAux denominator ibox178 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox178) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_178
private noncomputable def tree177 : TapeTree := .split 1 (((25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree178 tree179
attribute [irreducible] tree177
private theorem accepted_177 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox177) tree177 = true := by
  simp only [tree177,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox177 1 (25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) false,decode_split denominator ibox177 1 (25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_178 h,accepted_179 h⟩
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
private noncomputable def tree175 : TapeTree := .centered (candidateRows ibox175) (candidateRows (FixedTape.midBox ibox175))
attribute [irreducible] tree175
private theorem sign_175 : 2*denominator*(computed denominator (FixedTape.midBox ibox175)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox175).gradient k).lo.natAbs ((computed denominator ibox175).gradient k).hi.natAbs : Int)*((ibox175 k).hi-(ibox175 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox175
    (computed denominator ibox175) (computed denominator (FixedTape.midBox ibox175))
    (by decide +kernel)
private theorem midpoint_even_175 : ∀ k, 2 ∣ (ibox175 k).lo+(ibox175 k).hi := by decide +kernel
private theorem accepted_175 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox175) tree175 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox175 midpoint_even_175
  simp only [tree175,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox175,candidate_valid h (FixedTape.midBox ibox175),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox175 113 (FixedTape.rowsAux denominator ibox175 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox175) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_175
private noncomputable def tree174 : TapeTree := .split 1 (((25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree175 tree176
attribute [irreducible] tree174
private theorem accepted_174 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox174) tree174 = true := by
  simp only [tree174,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox174 1 (25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) false,decode_split denominator ibox174 1 (25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_175 h,accepted_176 h⟩
private noncomputable def tree173 : TapeTree := .split 2 (((22646009290519745643815880831724370094816550140711065385165473498687078400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree174 tree177
attribute [irreducible] tree173
private theorem accepted_173 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox173) tree173 = true := by
  simp only [tree173,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox173 2 (22646009290519745643815880831724370094816550140711065385165473498687078400000000000000000000000 : Int) false,decode_split denominator ibox173 2 (22646009290519745643815880831724370094816550140711065385165473498687078400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_174 h,accepted_177 h⟩
private noncomputable def tree172 : TapeTree := .split 1 (((30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree173 tree180
attribute [irreducible] tree172
private theorem accepted_172 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox172) tree172 = true := by
  simp only [tree172,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox172 1 (30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) false,decode_split denominator ibox172 1 (30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_173 h,accepted_180 h⟩
private noncomputable def tree171 : TapeTree := .split 2 (((25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree172 tree187
attribute [irreducible] tree171
private theorem accepted_171 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox171) tree171 = true := by
  simp only [tree171,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox171 2 (25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) false,decode_split denominator ibox171 2 (25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_172 h,accepted_187 h⟩
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
private noncomputable def tree168 : TapeTree := .split 2 (((28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree169 tree170
attribute [irreducible] tree168
private theorem accepted_168 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox168) tree168 = true := by
  simp only [tree168,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox168 2 (28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000 : Int) false,decode_split denominator ibox168 2 (28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000 : Int) true]
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
private noncomputable def tree165 : TapeTree := .split 2 (((28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree166 tree167
attribute [irreducible] tree165
private theorem accepted_165 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox165) tree165 = true := by
  simp only [tree165,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox165 2 (28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000 : Int) false,decode_split denominator ibox165 2 (28936567426775230544875847729425584010043369624241916881044771692766822400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_166 h,accepted_167 h⟩
private noncomputable def tree164 : TapeTree := .split 1 (((10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree165 tree168
attribute [irreducible] tree164
private theorem accepted_164 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox164) tree164 = true := by
  simp only [tree164,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox164 1 (10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) false,decode_split denominator ibox164 1 (10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_165 h,accepted_168 h⟩
private noncomputable def tree163 : TapeTree := .centered (candidateRows ibox163) (candidateRows (FixedTape.midBox ibox163))
attribute [irreducible] tree163
private theorem sign_163 : 2*denominator*(computed denominator (FixedTape.midBox ibox163)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox163).gradient k).lo.natAbs ((computed denominator ibox163).gradient k).hi.natAbs : Int)*((ibox163 k).hi-(ibox163 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox163
    (computed denominator ibox163) (computed denominator (FixedTape.midBox ibox163))
    (by decide +kernel)
private theorem midpoint_even_163 : ∀ k, 2 ∣ (ibox163 k).lo+(ibox163 k).hi := by decide +kernel
private theorem accepted_163 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox163) tree163 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox163 midpoint_even_163
  simp only [tree163,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox163,candidate_valid h (FixedTape.midBox ibox163),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox163 113 (FixedTape.rowsAux denominator ibox163 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox163) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_163
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
private noncomputable def tree161 : TapeTree := .split 2 (((26420344172273036584451860970345098443952641830829576282693052415134924800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree162 tree163
attribute [irreducible] tree161
private theorem accepted_161 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox161) tree161 = true := by
  simp only [tree161,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox161 2 (26420344172273036584451860970345098443952641830829576282693052415134924800000000000000000000000 : Int) false,decode_split denominator ibox161 2 (26420344172273036584451860970345098443952641830829576282693052415134924800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_162 h,accepted_163 h⟩
private noncomputable def tree160 : TapeTree := .centered (candidateRows ibox160) (candidateRows (FixedTape.midBox ibox160))
attribute [irreducible] tree160
private theorem sign_160 : 2*denominator*(computed denominator (FixedTape.midBox ibox160)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox160).gradient k).lo.natAbs ((computed denominator ibox160).gradient k).hi.natAbs : Int)*((ibox160 k).hi-(ibox160 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox160
    (computed denominator ibox160) (computed denominator (FixedTape.midBox ibox160))
    (by decide +kernel)
private theorem midpoint_even_160 : ∀ k, 2 ∣ (ibox160 k).lo+(ibox160 k).hi := by decide +kernel
private theorem accepted_160 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox160) tree160 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox160 midpoint_even_160
  simp only [tree160,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox160,candidate_valid h (FixedTape.midBox ibox160),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox160 113 (FixedTape.rowsAux denominator ibox160 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox160) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_160
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
private noncomputable def tree158 : TapeTree := .split 1 (((5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree159 tree160
attribute [irreducible] tree158
private theorem accepted_158 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox158) tree158 = true := by
  simp only [tree158,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox158 1 (5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 : Int) false,decode_split denominator ibox158 1 (5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_159 h,accepted_160 h⟩
private noncomputable def tree157 : TapeTree := .split 1 (((10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree158 tree161
attribute [irreducible] tree157
private theorem accepted_157 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox157) tree157 = true := by
  simp only [tree157,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox157 1 (10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) false,decode_split denominator ibox157 1 (10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_158 h,accepted_161 h⟩
private noncomputable def tree156 : TapeTree := .split 2 (((27678455799524133564663854349885341226998005727535746581868912053950873600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree157 tree164
attribute [irreducible] tree156
private theorem accepted_156 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox156) tree156 = true := by
  simp only [tree156,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox156 2 (27678455799524133564663854349885341226998005727535746581868912053950873600000000000000000000000 : Int) false,decode_split denominator ibox156 2 (27678455799524133564663854349885341226998005727535746581868912053950873600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_157 h,accepted_164 h⟩
private noncomputable def tree155 : TapeTree := .centered (candidateRows ibox155) (candidateRows (FixedTape.midBox ibox155))
attribute [irreducible] tree155
private theorem sign_155 : 2*denominator*(computed denominator (FixedTape.midBox ibox155)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox155).gradient k).lo.natAbs ((computed denominator ibox155).gradient k).hi.natAbs : Int)*((ibox155 k).hi-(ibox155 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox155
    (computed denominator ibox155) (computed denominator (FixedTape.midBox ibox155))
    (by decide +kernel)
private theorem midpoint_even_155 : ∀ k, 2 ∣ (ibox155 k).lo+(ibox155 k).hi := by decide +kernel
private theorem accepted_155 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox155) tree155 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox155 midpoint_even_155
  simp only [tree155,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox155,candidate_valid h (FixedTape.midBox ibox155),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox155 113 (FixedTape.rowsAux denominator ibox155 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox155) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_155
private noncomputable def tree154 : TapeTree := .centered (candidateRows ibox154) (candidateRows (FixedTape.midBox ibox154))
attribute [irreducible] tree154
private theorem sign_154 : 2*denominator*(computed denominator (FixedTape.midBox ibox154)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox154).gradient k).lo.natAbs ((computed denominator ibox154).gradient k).hi.natAbs : Int)*((ibox154 k).hi-(ibox154 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox154
    (computed denominator ibox154) (computed denominator (FixedTape.midBox ibox154))
    (by decide +kernel)
private theorem midpoint_even_154 : ∀ k, 2 ∣ (ibox154 k).lo+(ibox154 k).hi := by decide +kernel
private theorem accepted_154 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox154) tree154 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox154 midpoint_even_154
  simp only [tree154,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox154,candidate_valid h (FixedTape.midBox ibox154),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox154 113 (FixedTape.rowsAux denominator ibox154 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox154) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_154
private noncomputable def tree153 : TapeTree := .split 1 (((15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree154 tree155
attribute [irreducible] tree153
private theorem accepted_153 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox153) tree153 = true := by
  simp only [tree153,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox153 1 (15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) false,decode_split denominator ibox153 1 (15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_154 h,accepted_155 h⟩
private noncomputable def tree152 : TapeTree := .centered (candidateRows ibox152) (candidateRows (FixedTape.midBox ibox152))
attribute [irreducible] tree152
private theorem sign_152 : 2*denominator*(computed denominator (FixedTape.midBox ibox152)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox152).gradient k).lo.natAbs ((computed denominator ibox152).gradient k).hi.natAbs : Int)*((ibox152 k).hi-(ibox152 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox152
    (computed denominator ibox152) (computed denominator (FixedTape.midBox ibox152))
    (by decide +kernel)
private theorem midpoint_even_152 : ∀ k, 2 ∣ (ibox152 k).lo+(ibox152 k).hi := by decide +kernel
private theorem accepted_152 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox152) tree152 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox152 midpoint_even_152
  simp only [tree152,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox152,candidate_valid h (FixedTape.midBox ibox152),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox152 113 (FixedTape.rowsAux denominator ibox152 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox152) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_152
private noncomputable def tree151 : TapeTree := .split 2 (((22646009290519745643815880831724370094816550140711065385165473498687078400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree152 tree153
attribute [irreducible] tree151
private theorem accepted_151 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox151) tree151 = true := by
  simp only [tree151,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox151 2 (22646009290519745643815880831724370094816550140711065385165473498687078400000000000000000000000 : Int) false,decode_split denominator ibox151 2 (22646009290519745643815880831724370094816550140711065385165473498687078400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_152 h,accepted_153 h⟩
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
private noncomputable def tree148 : TapeTree := .split 1 (((5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree149 tree150
attribute [irreducible] tree148
private theorem accepted_148 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox148) tree148 = true := by
  simp only [tree148,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox148 1 (5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 : Int) false,decode_split denominator ibox148 1 (5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 : Int) true]
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
private noncomputable def tree146 : TapeTree := .split 2 (((22646009290519745643815880831724370094816550140711065385165473498687078400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree147 tree148
attribute [irreducible] tree146
private theorem accepted_146 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox146) tree146 = true := by
  simp only [tree146,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox146 2 (22646009290519745643815880831724370094816550140711065385165473498687078400000000000000000000000 : Int) false,decode_split denominator ibox146 2 (22646009290519745643815880831724370094816550140711065385165473498687078400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_147 h,accepted_148 h⟩
private noncomputable def tree145 : TapeTree := .split 1 (((10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree146 tree151
attribute [irreducible] tree145
private theorem accepted_145 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox145) tree145 = true := by
  simp only [tree145,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox145 1 (10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) false,decode_split denominator ibox145 1 (10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_146 h,accepted_151 h⟩
private noncomputable def tree144 : TapeTree := .split 2 (((25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree145 tree156
attribute [irreducible] tree144
private theorem accepted_144 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox144) tree144 = true := by
  simp only [tree144,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox144 2 (25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) false,decode_split denominator ibox144 2 (25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_145 h,accepted_156 h⟩
private noncomputable def tree143 : TapeTree := .split 1 (((20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree144 tree171
attribute [irreducible] tree143
private theorem accepted_143 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox143) tree143 = true := by
  simp only [tree143,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox143 1 (20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 : Int) false,decode_split denominator ibox143 1 (20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_144 h,accepted_171 h⟩
private noncomputable def tree142 : TapeTree := .split 2 (((30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree143 tree202
attribute [irreducible] tree142
private theorem accepted_142 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox142) tree142 = true := by
  simp only [tree142,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox142 2 (30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) false,decode_split denominator ibox142 2 (30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_143 h,accepted_202 h⟩
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
private noncomputable def tree139 : TapeTree := .split 0 (((29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) : ℚ)/(denominator : ℚ)) tree140 tree141
attribute [irreducible] tree139
private theorem accepted_139 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox139) tree139 = true := by
  simp only [tree139,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox139 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) false,decode_split denominator ibox139 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_140 h,accepted_141 h⟩
private noncomputable def tree138 : TapeTree := .centered (candidateRows ibox138) (candidateRows (FixedTape.midBox ibox138))
attribute [irreducible] tree138
private theorem sign_138 : 2*denominator*(computed denominator (FixedTape.midBox ibox138)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox138).gradient k).lo.natAbs ((computed denominator ibox138).gradient k).hi.natAbs : Int)*((ibox138 k).hi-(ibox138 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox138
    (computed denominator ibox138) (computed denominator (FixedTape.midBox ibox138))
    (by decide +kernel)
private theorem midpoint_even_138 : ∀ k, 2 ∣ (ibox138 k).lo+(ibox138 k).hi := by decide +kernel
private theorem accepted_138 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox138) tree138 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox138 midpoint_even_138
  simp only [tree138,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox138,candidate_valid h (FixedTape.midBox ibox138),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox138 113 (FixedTape.rowsAux denominator ibox138 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox138) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_138
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
private noncomputable def tree136 : TapeTree := .split 0 (((29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) : ℚ)/(denominator : ℚ)) tree137 tree138
attribute [irreducible] tree136
private theorem accepted_136 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox136) tree136 = true := by
  simp only [tree136,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox136 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) false,decode_split denominator ibox136 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_137 h,accepted_138 h⟩
private noncomputable def tree135 : TapeTree := .split 2 (((17613562781515357722967907313563398962635094553886384188462034943423283200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree136 tree139
attribute [irreducible] tree135
private theorem accepted_135 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox135) tree135 = true := by
  simp only [tree135,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox135 2 (17613562781515357722967907313563398962635094553886384188462034943423283200000000000000000000000 : Int) false,decode_split denominator ibox135 2 (17613562781515357722967907313563398962635094553886384188462034943423283200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_136 h,accepted_139 h⟩
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
private noncomputable def tree133 : TapeTree := .centered (candidateRows ibox133) (candidateRows (FixedTape.midBox ibox133))
attribute [irreducible] tree133
private theorem sign_133 : 2*denominator*(computed denominator (FixedTape.midBox ibox133)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox133).gradient k).lo.natAbs ((computed denominator ibox133).gradient k).hi.natAbs : Int)*((ibox133 k).hi-(ibox133 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox133
    (computed denominator ibox133) (computed denominator (FixedTape.midBox ibox133))
    (by decide +kernel)
private theorem midpoint_even_133 : ∀ k, 2 ∣ (ibox133 k).lo+(ibox133 k).hi := by decide +kernel
private theorem accepted_133 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox133) tree133 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox133 midpoint_even_133
  simp only [tree133,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox133,candidate_valid h (FixedTape.midBox ibox133),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox133 113 (FixedTape.rowsAux denominator ibox133 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox133) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_133
private noncomputable def tree132 : TapeTree := .split 2 (((17613562781515357722967907313563398962635094553886384188462034943423283200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree133 tree134
attribute [irreducible] tree132
private theorem accepted_132 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox132) tree132 = true := by
  simp only [tree132,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox132 2 (17613562781515357722967907313563398962635094553886384188462034943423283200000000000000000000000 : Int) false,decode_split denominator ibox132 2 (17613562781515357722967907313563398962635094553886384188462034943423283200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_133 h,accepted_134 h⟩
private noncomputable def tree131 : TapeTree := .split 1 (((35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree132 tree135
attribute [irreducible] tree131
private theorem accepted_131 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox131) tree131 = true := by
  simp only [tree131,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox131 1 (35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) false,decode_split denominator ibox131 1 (35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_132 h,accepted_135 h⟩
private noncomputable def tree130 : TapeTree := .centered (candidateRows ibox130) (candidateRows (FixedTape.midBox ibox130))
attribute [irreducible] tree130
private theorem sign_130 : 2*denominator*(computed denominator (FixedTape.midBox ibox130)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox130).gradient k).lo.natAbs ((computed denominator ibox130).gradient k).hi.natAbs : Int)*((ibox130 k).hi-(ibox130 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox130
    (computed denominator ibox130) (computed denominator (FixedTape.midBox ibox130))
    (by decide +kernel)
private theorem midpoint_even_130 : ∀ k, 2 ∣ (ibox130 k).lo+(ibox130 k).hi := by decide +kernel
private theorem accepted_130 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox130) tree130 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox130 midpoint_even_130
  simp only [tree130,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox130,candidate_valid h (FixedTape.midBox ibox130),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox130 113 (FixedTape.rowsAux denominator ibox130 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox130) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_130
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
private noncomputable def tree128 : TapeTree := .split 0 (((29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) : ℚ)/(denominator : ℚ)) tree129 tree130
attribute [irreducible] tree128
private theorem accepted_128 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox128) tree128 = true := by
  simp only [tree128,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox128 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) false,decode_split denominator ibox128 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_129 h,accepted_130 h⟩
private noncomputable def tree127 : TapeTree := .centered (candidateRows ibox127) (candidateRows (FixedTape.midBox ibox127))
attribute [irreducible] tree127
private theorem sign_127 : 2*denominator*(computed denominator (FixedTape.midBox ibox127)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox127).gradient k).lo.natAbs ((computed denominator ibox127).gradient k).hi.natAbs : Int)*((ibox127 k).hi-(ibox127 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox127
    (computed denominator ibox127) (computed denominator (FixedTape.midBox ibox127))
    (by decide +kernel)
private theorem midpoint_even_127 : ∀ k, 2 ∣ (ibox127 k).lo+(ibox127 k).hi := by decide +kernel
private theorem accepted_127 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox127) tree127 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox127 midpoint_even_127
  simp only [tree127,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox127,candidate_valid h (FixedTape.midBox ibox127),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox127 113 (FixedTape.rowsAux denominator ibox127 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox127) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_127
private noncomputable def tree126 : TapeTree := .split 1 (((37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree127 tree128
attribute [irreducible] tree126
private theorem accepted_126 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox126) tree126 = true := by
  simp only [tree126,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox126 1 (37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 : Int) false,decode_split denominator ibox126 1 (37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_127 h,accepted_128 h⟩
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
private noncomputable def tree124 : TapeTree := .centered (candidateRows ibox124) (candidateRows (FixedTape.midBox ibox124))
attribute [irreducible] tree124
private theorem sign_124 : 2*denominator*(computed denominator (FixedTape.midBox ibox124)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox124).gradient k).lo.natAbs ((computed denominator ibox124).gradient k).hi.natAbs : Int)*((ibox124 k).hi-(ibox124 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox124
    (computed denominator ibox124) (computed denominator (FixedTape.midBox ibox124))
    (by decide +kernel)
private theorem midpoint_even_124 : ∀ k, 2 ∣ (ibox124 k).lo+(ibox124 k).hi := by decide +kernel
private theorem accepted_124 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox124) tree124 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox124 midpoint_even_124
  simp only [tree124,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox124,candidate_valid h (FixedTape.midBox ibox124),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox124 113 (FixedTape.rowsAux denominator ibox124 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox124) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_124
private noncomputable def tree123 : TapeTree := .split 0 (((29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) : ℚ)/(denominator : ℚ)) tree124 tree125
attribute [irreducible] tree123
private theorem accepted_123 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox123) tree123 = true := by
  simp only [tree123,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox123 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) false,decode_split denominator ibox123 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_124 h,accepted_125 h⟩
private noncomputable def tree122 : TapeTree := .centered (candidateRows ibox122) (candidateRows (FixedTape.midBox ibox122))
attribute [irreducible] tree122
private theorem sign_122 : 2*denominator*(computed denominator (FixedTape.midBox ibox122)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox122).gradient k).lo.natAbs ((computed denominator ibox122).gradient k).hi.natAbs : Int)*((ibox122 k).hi-(ibox122 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox122
    (computed denominator ibox122) (computed denominator (FixedTape.midBox ibox122))
    (by decide +kernel)
private theorem midpoint_even_122 : ∀ k, 2 ∣ (ibox122 k).lo+(ibox122 k).hi := by decide +kernel
private theorem accepted_122 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox122) tree122 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox122 midpoint_even_122
  simp only [tree122,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox122,candidate_valid h (FixedTape.midBox ibox122),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox122 113 (FixedTape.rowsAux denominator ibox122 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox122) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_122
private noncomputable def tree121 : TapeTree := .split 1 (((37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree122 tree123
attribute [irreducible] tree121
private theorem accepted_121 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox121) tree121 = true := by
  simp only [tree121,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox121 1 (37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 : Int) false,decode_split denominator ibox121 1 (37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_122 h,accepted_123 h⟩
private noncomputable def tree120 : TapeTree := .split 2 (((12581116272510969802119933795402427830453638967061702991758596388159488000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree121 tree126
attribute [irreducible] tree120
private theorem accepted_120 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox120) tree120 = true := by
  simp only [tree120,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox120 2 (12581116272510969802119933795402427830453638967061702991758596388159488000000000000000000000000 : Int) false,decode_split denominator ibox120 2 (12581116272510969802119933795402427830453638967061702991758596388159488000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_121 h,accepted_126 h⟩
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
private noncomputable def tree117 : TapeTree := .centered (candidateRows ibox117) (candidateRows (FixedTape.midBox ibox117))
attribute [irreducible] tree117
private theorem sign_117 : 2*denominator*(computed denominator (FixedTape.midBox ibox117)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox117).gradient k).lo.natAbs ((computed denominator ibox117).gradient k).hi.natAbs : Int)*((ibox117 k).hi-(ibox117 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox117
    (computed denominator ibox117) (computed denominator (FixedTape.midBox ibox117))
    (by decide +kernel)
private theorem midpoint_even_117 : ∀ k, 2 ∣ (ibox117 k).lo+(ibox117 k).hi := by decide +kernel
private theorem accepted_117 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox117) tree117 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox117 midpoint_even_117
  simp only [tree117,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox117,candidate_valid h (FixedTape.midBox ibox117),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox117 113 (FixedTape.rowsAux denominator ibox117 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox117) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_117
private noncomputable def tree116 : TapeTree := .split 1 (((32710902308528521485511827868046312359179461314360427778572350609214668800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree117 tree118
attribute [irreducible] tree116
private theorem accepted_116 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox116) tree116 = true := by
  simp only [tree116,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox116 1 (32710902308528521485511827868046312359179461314360427778572350609214668800000000000000000000000 : Int) false,decode_split denominator ibox116 1 (32710902308528521485511827868046312359179461314360427778572350609214668800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_117 h,accepted_118 h⟩
private noncomputable def tree115 : TapeTree := .split 2 (((12581116272510969802119933795402427830453638967061702991758596388159488000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree116 tree119
attribute [irreducible] tree115
private theorem accepted_115 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox115) tree115 = true := by
  simp only [tree115,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox115 2 (12581116272510969802119933795402427830453638967061702991758596388159488000000000000000000000000 : Int) false,decode_split denominator ibox115 2 (12581116272510969802119933795402427830453638967061702991758596388159488000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_116 h,accepted_119 h⟩
private noncomputable def tree114 : TapeTree := .split 1 (((35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree115 tree120
attribute [irreducible] tree114
private theorem accepted_114 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox114) tree114 = true := by
  simp only [tree114,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox114 1 (35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) false,decode_split denominator ibox114 1 (35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_115 h,accepted_120 h⟩
private noncomputable def tree113 : TapeTree := .split 2 (((15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree114 tree131
attribute [irreducible] tree113
private theorem accepted_113 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox113) tree113 = true := by
  simp only [tree113,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox113 2 (15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) false,decode_split denominator ibox113 2 (15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_114 h,accepted_131 h⟩
private noncomputable def tree112 : TapeTree := .centered (candidateRows ibox112) (candidateRows (FixedTape.midBox ibox112))
attribute [irreducible] tree112
private theorem sign_112 : 2*denominator*(computed denominator (FixedTape.midBox ibox112)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox112).gradient k).lo.natAbs ((computed denominator ibox112).gradient k).hi.natAbs : Int)*((ibox112 k).hi-(ibox112 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox112
    (computed denominator ibox112) (computed denominator (FixedTape.midBox ibox112))
    (by decide +kernel)
private theorem midpoint_even_112 : ∀ k, 2 ∣ (ibox112 k).lo+(ibox112 k).hi := by decide +kernel
private theorem accepted_112 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox112) tree112 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox112 midpoint_even_112
  simp only [tree112,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox112,candidate_valid h (FixedTape.midBox ibox112),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox112 113 (FixedTape.rowsAux denominator ibox112 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox112) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_112
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
private noncomputable def tree110 : TapeTree := .split 2 (((17613562781515357722967907313563398962635094553886384188462034943423283200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree111 tree112
attribute [irreducible] tree110
private theorem accepted_110 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox110) tree110 = true := by
  simp only [tree110,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox110 2 (17613562781515357722967907313563398962635094553886384188462034943423283200000000000000000000000 : Int) false,decode_split denominator ibox110 2 (17613562781515357722967907313563398962635094553886384188462034943423283200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_111 h,accepted_112 h⟩
private noncomputable def tree109 : TapeTree := .centered (candidateRows ibox109) (candidateRows (FixedTape.midBox ibox109))
attribute [irreducible] tree109
private theorem sign_109 : 2*denominator*(computed denominator (FixedTape.midBox ibox109)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox109).gradient k).lo.natAbs ((computed denominator ibox109).gradient k).hi.natAbs : Int)*((ibox109 k).hi-(ibox109 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox109
    (computed denominator ibox109) (computed denominator (FixedTape.midBox ibox109))
    (by decide +kernel)
private theorem midpoint_even_109 : ∀ k, 2 ∣ (ibox109 k).lo+(ibox109 k).hi := by decide +kernel
private theorem accepted_109 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox109) tree109 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox109 midpoint_even_109
  simp only [tree109,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox109,candidate_valid h (FixedTape.midBox ibox109),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox109 113 (FixedTape.rowsAux denominator ibox109 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox109) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_109
private noncomputable def tree108 : TapeTree := .split 1 (((25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree109 tree110
attribute [irreducible] tree108
private theorem accepted_108 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox108) tree108 = true := by
  simp only [tree108,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox108 1 (25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) false,decode_split denominator ibox108 1 (25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_109 h,accepted_110 h⟩
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
private noncomputable def tree106 : TapeTree := .centered (candidateRows ibox106) (candidateRows (FixedTape.midBox ibox106))
attribute [irreducible] tree106
private theorem sign_106 : 2*denominator*(computed denominator (FixedTape.midBox ibox106)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox106).gradient k).lo.natAbs ((computed denominator ibox106).gradient k).hi.natAbs : Int)*((ibox106 k).hi-(ibox106 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox106
    (computed denominator ibox106) (computed denominator (FixedTape.midBox ibox106))
    (by decide +kernel)
private theorem midpoint_even_106 : ∀ k, 2 ∣ (ibox106 k).lo+(ibox106 k).hi := by decide +kernel
private theorem accepted_106 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox106) tree106 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox106 midpoint_even_106
  simp only [tree106,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox106,candidate_valid h (FixedTape.midBox ibox106),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox106 113 (FixedTape.rowsAux denominator ibox106 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox106) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_106
private noncomputable def tree105 : TapeTree := .split 2 (((12581116272510969802119933795402427830453638967061702991758596388159488000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree106 tree107
attribute [irreducible] tree105
private theorem accepted_105 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox105) tree105 = true := by
  simp only [tree105,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox105 2 (12581116272510969802119933795402427830453638967061702991758596388159488000000000000000000000000 : Int) false,decode_split denominator ibox105 2 (12581116272510969802119933795402427830453638967061702991758596388159488000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_106 h,accepted_107 h⟩
private noncomputable def tree104 : TapeTree := .centered (candidateRows ibox104) (candidateRows (FixedTape.midBox ibox104))
attribute [irreducible] tree104
private theorem sign_104 : 2*denominator*(computed denominator (FixedTape.midBox ibox104)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox104).gradient k).lo.natAbs ((computed denominator ibox104).gradient k).hi.natAbs : Int)*((ibox104 k).hi-(ibox104 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox104
    (computed denominator ibox104) (computed denominator (FixedTape.midBox ibox104))
    (by decide +kernel)
private theorem midpoint_even_104 : ∀ k, 2 ∣ (ibox104 k).lo+(ibox104 k).hi := by decide +kernel
private theorem accepted_104 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox104) tree104 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox104 midpoint_even_104
  simp only [tree104,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox104,candidate_valid h (FixedTape.midBox ibox104),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox104 113 (FixedTape.rowsAux denominator ibox104 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox104) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_104
private noncomputable def tree103 : TapeTree := .split 1 (((25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree104 tree105
attribute [irreducible] tree103
private theorem accepted_103 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox103) tree103 = true := by
  simp only [tree103,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox103 1 (25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) false,decode_split denominator ibox103 1 (25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_104 h,accepted_105 h⟩
private noncomputable def tree102 : TapeTree := .split 2 (((15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree103 tree108
attribute [irreducible] tree102
private theorem accepted_102 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox102) tree102 = true := by
  simp only [tree102,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox102 2 (15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) false,decode_split denominator ibox102 2 (15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_103 h,accepted_108 h⟩
private noncomputable def tree101 : TapeTree := .split 1 (((30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree102 tree113
attribute [irreducible] tree101
private theorem accepted_101 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox101) tree101 = true := by
  simp only [tree101,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox101 1 (30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) false,decode_split denominator ibox101 1 (30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_102 h,accepted_113 h⟩
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
private noncomputable def tree99 : TapeTree := .face 1 true (candidateRows ibox99) tree100
attribute [irreducible] tree99
private theorem sign_99 : 0 ≤ ((computed denominator ibox99).gradient 1).lo := by decide +kernel
private theorem accepted_99 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox99) tree99 = true := by
  simp only [tree99,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox99,?_,accepted_100 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox99)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox99).gradient 1).lo) denominator_positive).2 sign_99
private noncomputable def tree98 : TapeTree := .centered (candidateRows ibox98) (candidateRows (FixedTape.midBox ibox98))
attribute [irreducible] tree98
private theorem sign_98 : 2*denominator*(computed denominator (FixedTape.midBox ibox98)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox98).gradient k).lo.natAbs ((computed denominator ibox98).gradient k).hi.natAbs : Int)*((ibox98 k).hi-(ibox98 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox98
    (computed denominator ibox98) (computed denominator (FixedTape.midBox ibox98))
    (by decide +kernel)
private theorem midpoint_even_98 : ∀ k, 2 ∣ (ibox98 k).lo+(ibox98 k).hi := by decide +kernel
private theorem accepted_98 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox98) tree98 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox98 midpoint_even_98
  simp only [tree98,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox98,candidate_valid h (FixedTape.midBox ibox98),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox98 113 (FixedTape.rowsAux denominator ibox98 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox98) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_98
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
private noncomputable def tree96 : TapeTree := .split 0 (((29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) : ℚ)/(denominator : ℚ)) tree97 tree99
attribute [irreducible] tree96
private theorem accepted_96 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox96) tree96 = true := by
  simp only [tree96,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox96 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) false,decode_split denominator ibox96 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_97 h,accepted_99 h⟩
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
private noncomputable def tree94 : TapeTree := .face 1 true (candidateRows ibox94) tree95
attribute [irreducible] tree94
private theorem sign_94 : 0 ≤ ((computed denominator ibox94).gradient 1).lo := by decide +kernel
private theorem accepted_94 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox94) tree94 = true := by
  simp only [tree94,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox94,?_,accepted_95 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox94)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox94).gradient 1).lo) denominator_positive).2 sign_94
private noncomputable def tree93 : TapeTree := .centered (candidateRows ibox93) (candidateRows (FixedTape.midBox ibox93))
attribute [irreducible] tree93
private theorem sign_93 : 2*denominator*(computed denominator (FixedTape.midBox ibox93)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox93).gradient k).lo.natAbs ((computed denominator ibox93).gradient k).hi.natAbs : Int)*((ibox93 k).hi-(ibox93 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox93
    (computed denominator ibox93) (computed denominator (FixedTape.midBox ibox93))
    (by decide +kernel)
private theorem midpoint_even_93 : ∀ k, 2 ∣ (ibox93 k).lo+(ibox93 k).hi := by decide +kernel
private theorem accepted_93 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox93) tree93 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox93 midpoint_even_93
  simp only [tree93,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox93,candidate_valid h (FixedTape.midBox ibox93),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox93 113 (FixedTape.rowsAux denominator ibox93 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox93) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_93
private noncomputable def tree92 : TapeTree := .face 1 true (candidateRows ibox92) tree93
attribute [irreducible] tree92
private theorem sign_92 : 0 ≤ ((computed denominator ibox92).gradient 1).lo := by decide +kernel
private theorem accepted_92 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox92) tree92 = true := by
  simp only [tree92,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox92,?_,accepted_93 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox92)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox92).gradient 1).lo) denominator_positive).2 sign_92
private noncomputable def tree91 : TapeTree := .split 0 (((29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) : ℚ)/(denominator : ℚ)) tree92 tree94
attribute [irreducible] tree91
private theorem accepted_91 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox91) tree91 = true := by
  simp only [tree91,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox91 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) false,decode_split denominator ibox91 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_92 h,accepted_94 h⟩
private noncomputable def tree90 : TapeTree := .split 2 (((7548669763506581881271960277241456698272183380237021795055157832895692800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree91 tree96
attribute [irreducible] tree90
private theorem accepted_90 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox90) tree90 = true := by
  simp only [tree90,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox90 2 (7548669763506581881271960277241456698272183380237021795055157832895692800000000000000000000000 : Int) false,decode_split denominator ibox90 2 (7548669763506581881271960277241456698272183380237021795055157832895692800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_91 h,accepted_96 h⟩
private noncomputable def tree89 : TapeTree := .centered (candidateRows ibox89) (candidateRows (FixedTape.midBox ibox89))
attribute [irreducible] tree89
private theorem sign_89 : 2*denominator*(computed denominator (FixedTape.midBox ibox89)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox89).gradient k).lo.natAbs ((computed denominator ibox89).gradient k).hi.natAbs : Int)*((ibox89 k).hi-(ibox89 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox89
    (computed denominator ibox89) (computed denominator (FixedTape.midBox ibox89))
    (by decide +kernel)
private theorem midpoint_even_89 : ∀ k, 2 ∣ (ibox89 k).lo+(ibox89 k).hi := by decide +kernel
private theorem accepted_89 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox89) tree89 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox89 midpoint_even_89
  simp only [tree89,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox89,candidate_valid h (FixedTape.midBox ibox89),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox89 113 (FixedTape.rowsAux denominator ibox89 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox89) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_89
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
private noncomputable def tree87 : TapeTree := .split 0 (((29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) : ℚ)/(denominator : ℚ)) tree88 tree89
attribute [irreducible] tree87
private theorem accepted_87 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox87) tree87 = true := by
  simp only [tree87,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox87 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) false,decode_split denominator ibox87 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_88 h,accepted_89 h⟩
private noncomputable def tree86 : TapeTree := .centered (candidateRows ibox86) (candidateRows (FixedTape.midBox ibox86))
attribute [irreducible] tree86
private theorem sign_86 : 2*denominator*(computed denominator (FixedTape.midBox ibox86)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox86).gradient k).lo.natAbs ((computed denominator ibox86).gradient k).hi.natAbs : Int)*((ibox86 k).hi-(ibox86 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox86
    (computed denominator ibox86) (computed denominator (FixedTape.midBox ibox86))
    (by decide +kernel)
private theorem midpoint_even_86 : ∀ k, 2 ∣ (ibox86 k).lo+(ibox86 k).hi := by decide +kernel
private theorem accepted_86 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox86) tree86 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox86 midpoint_even_86
  simp only [tree86,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox86,candidate_valid h (FixedTape.midBox ibox86),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox86 113 (FixedTape.rowsAux denominator ibox86 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox86) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_86
private noncomputable def tree85 : TapeTree := .face 1 true (candidateRows ibox85) tree86
attribute [irreducible] tree85
private theorem sign_85 : 0 ≤ ((computed denominator ibox85).gradient 1).lo := by decide +kernel
private theorem accepted_85 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox85) tree85 = true := by
  simp only [tree85,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox85,?_,accepted_86 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox85)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox85).gradient 1).lo) denominator_positive).2 sign_85
private noncomputable def tree84 : TapeTree := .split 2 (((7548669763506581881271960277241456698272183380237021795055157832895692800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree85 tree87
attribute [irreducible] tree84
private theorem accepted_84 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox84) tree84 = true := by
  simp only [tree84,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox84 2 (7548669763506581881271960277241456698272183380237021795055157832895692800000000000000000000000 : Int) false,decode_split denominator ibox84 2 (7548669763506581881271960277241456698272183380237021795055157832895692800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_85 h,accepted_87 h⟩
private noncomputable def tree83 : TapeTree := .split 1 (((37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree84 tree90
attribute [irreducible] tree83
private theorem accepted_83 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox83) tree83 = true := by
  simp only [tree83,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox83 1 (37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 : Int) false,decode_split denominator ibox83 1 (37743348817532909406359801386207283491360916901185108975275789164478464000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_84 h,accepted_90 h⟩
private noncomputable def tree82 : TapeTree := .centered (candidateRows ibox82) (candidateRows (FixedTape.midBox ibox82))
attribute [irreducible] tree82
private theorem sign_82 : 2*denominator*(computed denominator (FixedTape.midBox ibox82)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox82).gradient k).lo.natAbs ((computed denominator ibox82).gradient k).hi.natAbs : Int)*((ibox82 k).hi-(ibox82 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox82
    (computed denominator ibox82) (computed denominator (FixedTape.midBox ibox82))
    (by decide +kernel)
private theorem midpoint_even_82 : ∀ k, 2 ∣ (ibox82 k).lo+(ibox82 k).hi := by decide +kernel
private theorem accepted_82 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox82) tree82 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox82 midpoint_even_82
  simp only [tree82,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox82,candidate_valid h (FixedTape.midBox ibox82),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox82 113 (FixedTape.rowsAux denominator ibox82 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox82) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_82
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
private noncomputable def tree80 : TapeTree := .split 2 (((7548669763506581881271960277241456698272183380237021795055157832895692800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree81 tree82
attribute [irreducible] tree80
private theorem accepted_80 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox80) tree80 = true := by
  simp only [tree80,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox80 2 (7548669763506581881271960277241456698272183380237021795055157832895692800000000000000000000000 : Int) false,decode_split denominator ibox80 2 (7548669763506581881271960277241456698272183380237021795055157832895692800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_81 h,accepted_82 h⟩
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
private noncomputable def tree78 : TapeTree := .split 1 (((32710902308528521485511827868046312359179461314360427778572350609214668800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree79 tree80
attribute [irreducible] tree78
private theorem accepted_78 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox78) tree78 = true := by
  simp only [tree78,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox78 1 (32710902308528521485511827868046312359179461314360427778572350609214668800000000000000000000000 : Int) false,decode_split denominator ibox78 1 (32710902308528521485511827868046312359179461314360427778572350609214668800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_79 h,accepted_80 h⟩
private noncomputable def tree77 : TapeTree := .split 1 (((35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree78 tree83
attribute [irreducible] tree77
private theorem accepted_77 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox77) tree77 = true := by
  simp only [tree77,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox77 1 (35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) false,decode_split denominator ibox77 1 (35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_78 h,accepted_83 h⟩
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
private noncomputable def tree74 : TapeTree := .split 0 (((29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) : ℚ)/(denominator : ℚ)) tree75 tree76
attribute [irreducible] tree74
private theorem accepted_74 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox74) tree74 = true := by
  simp only [tree74,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox74 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) false,decode_split denominator ibox74 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_75 h,accepted_76 h⟩
private noncomputable def tree73 : TapeTree := .centered (candidateRows ibox73) (candidateRows (FixedTape.midBox ibox73))
attribute [irreducible] tree73
private theorem sign_73 : 2*denominator*(computed denominator (FixedTape.midBox ibox73)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox73).gradient k).lo.natAbs ((computed denominator ibox73).gradient k).hi.natAbs : Int)*((ibox73 k).hi-(ibox73 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox73
    (computed denominator ibox73) (computed denominator (FixedTape.midBox ibox73))
    (by decide +kernel)
private theorem midpoint_even_73 : ∀ k, 2 ∣ (ibox73 k).lo+(ibox73 k).hi := by decide +kernel
private theorem accepted_73 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox73) tree73 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox73 midpoint_even_73
  simp only [tree73,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox73,candidate_valid h (FixedTape.midBox ibox73),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox73 113 (FixedTape.rowsAux denominator ibox73 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox73) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_73
private noncomputable def tree72 : TapeTree := .centered (candidateRows ibox72) (candidateRows (FixedTape.midBox ibox72))
attribute [irreducible] tree72
private theorem sign_72 : 2*denominator*(computed denominator (FixedTape.midBox ibox72)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox72).gradient k).lo.natAbs ((computed denominator ibox72).gradient k).hi.natAbs : Int)*((ibox72 k).hi-(ibox72 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox72
    (computed denominator ibox72) (computed denominator (FixedTape.midBox ibox72))
    (by decide +kernel)
private theorem midpoint_even_72 : ∀ k, 2 ∣ (ibox72 k).lo+(ibox72 k).hi := by decide +kernel
private theorem accepted_72 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox72) tree72 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox72 midpoint_even_72
  simp only [tree72,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox72,candidate_valid h (FixedTape.midBox ibox72),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox72 113 (FixedTape.rowsAux denominator ibox72 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox72) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_72
private noncomputable def tree71 : TapeTree := .split 0 (((29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) : ℚ)/(denominator : ℚ)) tree72 tree73
attribute [irreducible] tree71
private theorem accepted_71 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox71) tree71 = true := by
  simp only [tree71,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox71 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) false,decode_split denominator ibox71 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_72 h,accepted_73 h⟩
private noncomputable def tree70 : TapeTree := .split 2 (((3774334881753290940635980138620728349136091690118510897527578916447846400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree71 tree74
attribute [irreducible] tree70
private theorem accepted_70 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox70) tree70 = true := by
  simp only [tree70,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox70 2 (3774334881753290940635980138620728349136091690118510897527578916447846400000000000000000000000 : Int) false,decode_split denominator ibox70 2 (3774334881753290940635980138620728349136091690118510897527578916447846400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_71 h,accepted_74 h⟩
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
private noncomputable def tree68 : TapeTree := .centered (candidateRows ibox68) (candidateRows (FixedTape.midBox ibox68))
attribute [irreducible] tree68
private theorem sign_68 : 2*denominator*(computed denominator (FixedTape.midBox ibox68)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox68).gradient k).lo.natAbs ((computed denominator ibox68).gradient k).hi.natAbs : Int)*((ibox68 k).hi-(ibox68 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox68
    (computed denominator ibox68) (computed denominator (FixedTape.midBox ibox68))
    (by decide +kernel)
private theorem midpoint_even_68 : ∀ k, 2 ∣ (ibox68 k).lo+(ibox68 k).hi := by decide +kernel
private theorem accepted_68 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox68) tree68 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox68 midpoint_even_68
  simp only [tree68,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox68,candidate_valid h (FixedTape.midBox ibox68),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox68 113 (FixedTape.rowsAux denominator ibox68 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox68) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_68
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
private noncomputable def tree66 : TapeTree := .split 0 (((29251095333588002776950242472555476366615303334030006583256501872598330918624577894481920000000 : Int) : ℚ)/(denominator : ℚ)) tree67 tree68
attribute [irreducible] tree66
private theorem accepted_66 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox66) tree66 = true := by
  simp only [tree66,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox66 0 (29251095333588002776950242472555476366615303334030006583256501872598330918624577894481920000000 : Int) false,decode_split denominator ibox66 0 (29251095333588002776950242472555476366615303334030006583256501872598330918624577894481920000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_67 h,accepted_68 h⟩
private noncomputable def tree65 : TapeTree := .split 2 (((1887167440876645470317990069310364174568045845059255448763789458223923200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree66 tree69
attribute [irreducible] tree65
private theorem accepted_65 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox65) tree65 = true := by
  simp only [tree65,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox65 2 (1887167440876645470317990069310364174568045845059255448763789458223923200000000000000000000000 : Int) false,decode_split denominator ibox65 2 (1887167440876645470317990069310364174568045845059255448763789458223923200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_66 h,accepted_69 h⟩
private noncomputable def tree64 : TapeTree := .centered (candidateRows ibox64) (candidateRows (FixedTape.midBox ibox64))
attribute [irreducible] tree64
private theorem sign_64 : 2*denominator*(computed denominator (FixedTape.midBox ibox64)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox64).gradient k).lo.natAbs ((computed denominator ibox64).gradient k).hi.natAbs : Int)*((ibox64 k).hi-(ibox64 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox64
    (computed denominator ibox64) (computed denominator (FixedTape.midBox ibox64))
    (by decide +kernel)
private theorem midpoint_even_64 : ∀ k, 2 ∣ (ibox64 k).lo+(ibox64 k).hi := by decide +kernel
private theorem accepted_64 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox64) tree64 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox64 midpoint_even_64
  simp only [tree64,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox64,candidate_valid h (FixedTape.midBox ibox64),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox64 113 (FixedTape.rowsAux denominator ibox64 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox64) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_64
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
private noncomputable def tree61 : TapeTree := .split 0 (((29041410062379487955567312643802214795567347527504613448448681752710658572874859298160640000000 : Int) : ℚ)/(denominator : ℚ)) tree62 tree63
attribute [irreducible] tree61
private theorem accepted_61 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox61) tree61 = true := by
  simp only [tree61,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox61 0 (29041410062379487955567312643802214795567347527504613448448681752710658572874859298160640000000 : Int) false,decode_split denominator ibox61 0 (29041410062379487955567312643802214795567347527504613448448681752710658572874859298160640000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_62 h,accepted_63 h⟩
private noncomputable def tree60 : TapeTree := .split 2 (((1887167440876645470317990069310364174568045845059255448763789458223923200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree61 tree64
attribute [irreducible] tree60
private theorem accepted_60 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox60) tree60 = true := by
  simp only [tree60,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox60 2 (1887167440876645470317990069310364174568045845059255448763789458223923200000000000000000000000 : Int) false,decode_split denominator ibox60 2 (1887167440876645470317990069310364174568045845059255448763789458223923200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_61 h,accepted_64 h⟩
private noncomputable def tree59 : TapeTree := .split 0 (((29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) : ℚ)/(denominator : ℚ)) tree60 tree65
attribute [irreducible] tree59
private theorem accepted_59 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox59) tree59 = true := by
  simp only [tree59,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox59 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) false,decode_split denominator ibox59 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_60 h,accepted_65 h⟩
private noncomputable def tree58 : TapeTree := .centered (candidateRows ibox58) (candidateRows (FixedTape.midBox ibox58))
attribute [irreducible] tree58
private theorem sign_58 : 2*denominator*(computed denominator (FixedTape.midBox ibox58)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox58).gradient k).lo.natAbs ((computed denominator ibox58).gradient k).hi.natAbs : Int)*((ibox58 k).hi-(ibox58 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox58
    (computed denominator ibox58) (computed denominator (FixedTape.midBox ibox58))
    (by decide +kernel)
private theorem midpoint_even_58 : ∀ k, 2 ∣ (ibox58 k).lo+(ibox58 k).hi := by decide +kernel
private theorem accepted_58 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox58) tree58 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox58 midpoint_even_58
  simp only [tree58,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox58,candidate_valid h (FixedTape.midBox ibox58),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox58 113 (FixedTape.rowsAux denominator ibox58 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox58) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_58
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
private noncomputable def tree56 : TapeTree := .split 0 (((29251095333588002776950242472555476366615303334030006583256501872598330918624577894481920000000 : Int) : ℚ)/(denominator : ℚ)) tree57 tree58
attribute [irreducible] tree56
private theorem accepted_56 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox56) tree56 = true := by
  simp only [tree56,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox56 0 (29251095333588002776950242472555476366615303334030006583256501872598330918624577894481920000000 : Int) false,decode_split denominator ibox56 0 (29251095333588002776950242472555476366615303334030006583256501872598330918624577894481920000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_57 h,accepted_58 h⟩
private noncomputable def tree55 : TapeTree := .centered (candidateRows ibox55) (candidateRows (FixedTape.midBox ibox55))
attribute [irreducible] tree55
private theorem sign_55 : 2*denominator*(computed denominator (FixedTape.midBox ibox55)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox55).gradient k).lo.natAbs ((computed denominator ibox55).gradient k).hi.natAbs : Int)*((ibox55 k).hi-(ibox55 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox55
    (computed denominator ibox55) (computed denominator (FixedTape.midBox ibox55))
    (by decide +kernel)
private theorem midpoint_even_55 : ∀ k, 2 ∣ (ibox55 k).lo+(ibox55 k).hi := by decide +kernel
private theorem accepted_55 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox55) tree55 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox55 midpoint_even_55
  simp only [tree55,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox55,candidate_valid h (FixedTape.midBox ibox55),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox55 113 (FixedTape.rowsAux denominator ibox55 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox55) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_55
private noncomputable def tree54 : TapeTree := .face 2 false (candidateRows ibox54) tree55
attribute [irreducible] tree54
private theorem sign_54 : ((computed denominator ibox54).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_54 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox54) tree54 = true := by
  simp only [tree54,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox54,?_,accepted_55 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox54)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox54).gradient 2).hi) denominator_positive).1 sign_54
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
private noncomputable def tree52 : TapeTree := .face 2 false (candidateRows ibox52) tree53
attribute [irreducible] tree52
private theorem sign_52 : ((computed denominator ibox52).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_52 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox52) tree52 = true := by
  simp only [tree52,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox52,?_,accepted_53 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox52)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox52).gradient 2).hi) denominator_positive).1 sign_52
private noncomputable def tree51 : TapeTree := .split 0 (((29251095333588002776950242472555476366615303334030006583256501872598330918624577894481920000000 : Int) : ℚ)/(denominator : ℚ)) tree52 tree54
attribute [irreducible] tree51
private theorem accepted_51 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox51) tree51 = true := by
  simp only [tree51,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox51 0 (29251095333588002776950242472555476366615303334030006583256501872598330918624577894481920000000 : Int) false,decode_split denominator ibox51 0 (29251095333588002776950242472555476366615303334030006583256501872598330918624577894481920000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_52 h,accepted_54 h⟩
private noncomputable def tree50 : TapeTree := .split 2 (((629055813625548490105996689770121391522681948353085149587929819407974400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree51 tree56
attribute [irreducible] tree50
private theorem accepted_50 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox50) tree50 = true := by
  simp only [tree50,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox50 2 (629055813625548490105996689770121391522681948353085149587929819407974400000000000000000000000 : Int) false,decode_split denominator ibox50 2 (629055813625548490105996689770121391522681948353085149587929819407974400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_51 h,accepted_56 h⟩
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
private noncomputable def tree48 : TapeTree := .centered (candidateRows ibox48) (candidateRows (FixedTape.midBox ibox48))
attribute [irreducible] tree48
private theorem sign_48 : 2*denominator*(computed denominator (FixedTape.midBox ibox48)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox48).gradient k).lo.natAbs ((computed denominator ibox48).gradient k).hi.natAbs : Int)*((ibox48 k).hi-(ibox48 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox48
    (computed denominator ibox48) (computed denominator (FixedTape.midBox ibox48))
    (by decide +kernel)
private theorem midpoint_even_48 : ∀ k, 2 ∣ (ibox48 k).lo+(ibox48 k).hi := by decide +kernel
private theorem accepted_48 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox48) tree48 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox48 midpoint_even_48
  simp only [tree48,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox48,candidate_valid h (FixedTape.midBox ibox48),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox48 113 (FixedTape.rowsAux denominator ibox48 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox48) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_48
private noncomputable def tree47 : TapeTree := .split 0 (((29041410062379487955567312643802214795567347527504613448448681752710658572874859298160640000000 : Int) : ℚ)/(denominator : ℚ)) tree48 tree49
attribute [irreducible] tree47
private theorem accepted_47 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox47) tree47 = true := by
  simp only [tree47,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox47 0 (29041410062379487955567312643802214795567347527504613448448681752710658572874859298160640000000 : Int) false,decode_split denominator ibox47 0 (29041410062379487955567312643802214795567347527504613448448681752710658572874859298160640000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_48 h,accepted_49 h⟩
private noncomputable def tree46 : TapeTree := .centered (candidateRows ibox46) (candidateRows (FixedTape.midBox ibox46))
attribute [irreducible] tree46
private theorem sign_46 : 2*denominator*(computed denominator (FixedTape.midBox ibox46)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox46).gradient k).lo.natAbs ((computed denominator ibox46).gradient k).hi.natAbs : Int)*((ibox46 k).hi-(ibox46 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox46
    (computed denominator ibox46) (computed denominator (FixedTape.midBox ibox46))
    (by decide +kernel)
private theorem midpoint_even_46 : ∀ k, 2 ∣ (ibox46 k).lo+(ibox46 k).hi := by decide +kernel
private theorem accepted_46 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox46) tree46 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox46 midpoint_even_46
  simp only [tree46,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox46,candidate_valid h (FixedTape.midBox ibox46),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox46 113 (FixedTape.rowsAux denominator ibox46 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox46) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_46
private noncomputable def tree45 : TapeTree := .face 2 false (candidateRows ibox45) tree46
attribute [irreducible] tree45
private theorem sign_45 : ((computed denominator ibox45).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox45,?_,accepted_46 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox45)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox45).gradient 2).hi) denominator_positive).1 sign_45
private noncomputable def tree44 : TapeTree := .centered (candidateRows ibox44) (candidateRows (FixedTape.midBox ibox44))
attribute [irreducible] tree44
private theorem sign_44 : 2*denominator*(computed denominator (FixedTape.midBox ibox44)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox44).gradient k).lo.natAbs ((computed denominator ibox44).gradient k).hi.natAbs : Int)*((ibox44 k).hi-(ibox44 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox44
    (computed denominator ibox44) (computed denominator (FixedTape.midBox ibox44))
    (by decide +kernel)
private theorem midpoint_even_44 : ∀ k, 2 ∣ (ibox44 k).lo+(ibox44 k).hi := by decide +kernel
private theorem accepted_44 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox44) tree44 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox44 midpoint_even_44
  simp only [tree44,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox44,candidate_valid h (FixedTape.midBox ibox44),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox44 113 (FixedTape.rowsAux denominator ibox44 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox44) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_44
private noncomputable def tree43 : TapeTree := .face 2 false (candidateRows ibox43) tree44
attribute [irreducible] tree43
private theorem sign_43 : ((computed denominator ibox43).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_43 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox43) tree43 = true := by
  simp only [tree43,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox43,?_,accepted_44 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox43)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox43).gradient 2).hi) denominator_positive).1 sign_43
private noncomputable def tree42 : TapeTree := .split 0 (((29041410062379487955567312643802214795567347527504613448448681752710658572874859298160640000000 : Int) : ℚ)/(denominator : ℚ)) tree43 tree45
attribute [irreducible] tree42
private theorem accepted_42 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox42) tree42 = true := by
  simp only [tree42,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox42 0 (29041410062379487955567312643802214795567347527504613448448681752710658572874859298160640000000 : Int) false,decode_split denominator ibox42 0 (29041410062379487955567312643802214795567347527504613448448681752710658572874859298160640000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_43 h,accepted_45 h⟩
private noncomputable def tree41 : TapeTree := .split 2 (((629055813625548490105996689770121391522681948353085149587929819407974400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree42 tree47
attribute [irreducible] tree41
private theorem accepted_41 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox41) tree41 = true := by
  simp only [tree41,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox41 2 (629055813625548490105996689770121391522681948353085149587929819407974400000000000000000000000 : Int) false,decode_split denominator ibox41 2 (629055813625548490105996689770121391522681948353085149587929819407974400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_42 h,accepted_47 h⟩
private noncomputable def tree40 : TapeTree := .split 0 (((29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) : ℚ)/(denominator : ℚ)) tree41 tree50
attribute [irreducible] tree40
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox40 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) false,decode_split denominator ibox40 0 (29146252697983745366258777558178845581091325430767310015852591812654494745749718596321280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_41 h,accepted_50 h⟩
private noncomputable def tree39 : TapeTree := .split 2 (((1258111627251096980211993379540242783045363896706170299175859638815948800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree40 tree59
attribute [irreducible] tree39
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox39 2 (1258111627251096980211993379540242783045363896706170299175859638815948800000000000000000000000 : Int) false,decode_split denominator ibox39 2 (1258111627251096980211993379540242783045363896706170299175859638815948800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_40 h,accepted_59 h⟩
private noncomputable def tree38 : TapeTree := .split 2 (((2516223254502193960423986759080485566090727793412340598351719277631897600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree39 tree70
attribute [irreducible] tree38
private theorem accepted_38 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox38) tree38 = true := by
  simp only [tree38,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox38 2 (2516223254502193960423986759080485566090727793412340598351719277631897600000000000000000000000 : Int) false,decode_split denominator ibox38 2 (2516223254502193960423986759080485566090727793412340598351719277631897600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_39 h,accepted_70 h⟩
private noncomputable def tree37 : TapeTree := .face 1 true (candidateRows ibox37) tree38
attribute [irreducible] tree37
private theorem sign_37 : 0 ≤ ((computed denominator ibox37).gradient 1).lo := by decide +kernel
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox37,?_,accepted_38 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox37)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox37).gradient 1).lo) denominator_positive).2 sign_37
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
private noncomputable def tree35 : TapeTree := .face 1 true (candidateRows ibox35) tree36
attribute [irreducible] tree35
private theorem sign_35 : 0 ≤ ((computed denominator ibox35).gradient 1).lo := by decide +kernel
private theorem accepted_35 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox35) tree35 = true := by
  simp only [tree35,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox35,?_,accepted_36 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox35)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox35).gradient 1).lo) denominator_positive).2 sign_35
private noncomputable def tree34 : TapeTree := .split 1 (((35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree35 tree37
attribute [irreducible] tree34
private theorem accepted_34 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox34) tree34 = true := by
  simp only [tree34,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox34 1 (35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) false,decode_split denominator ibox34 1 (35227125563030715445935814627126797925270189107772768376924069886846566400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_35 h,accepted_37 h⟩
private noncomputable def tree33 : TapeTree := .split 2 (((5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree34 tree77
attribute [irreducible] tree33
private theorem accepted_33 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox33) tree33 = true := by
  simp only [tree33,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox33 2 (5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 : Int) false,decode_split denominator ibox33 2 (5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_34 h,accepted_77 h⟩
private noncomputable def tree32 : TapeTree := .centered (candidateRows ibox32) (candidateRows (FixedTape.midBox ibox32))
attribute [irreducible] tree32
private theorem sign_32 : 2*denominator*(computed denominator (FixedTape.midBox ibox32)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox32).gradient k).lo.natAbs ((computed denominator ibox32).gradient k).hi.natAbs : Int)*((ibox32 k).hi-(ibox32 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox32
    (computed denominator ibox32) (computed denominator (FixedTape.midBox ibox32))
    (by decide +kernel)
private theorem midpoint_even_32 : ∀ k, 2 ∣ (ibox32 k).lo+(ibox32 k).hi := by decide +kernel
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox32 midpoint_even_32
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox32,candidate_valid h (FixedTape.midBox ibox32),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox32 113 (FixedTape.rowsAux denominator ibox32 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox32) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_32
private noncomputable def tree31 : TapeTree := .centered (candidateRows ibox31) (candidateRows (FixedTape.midBox ibox31))
attribute [irreducible] tree31
private theorem sign_31 : 2*denominator*(computed denominator (FixedTape.midBox ibox31)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox31).gradient k).lo.natAbs ((computed denominator ibox31).gradient k).hi.natAbs : Int)*((ibox31 k).hi-(ibox31 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox31
    (computed denominator ibox31) (computed denominator (FixedTape.midBox ibox31))
    (by decide +kernel)
private theorem midpoint_even_31 : ∀ k, 2 ∣ (ibox31 k).lo+(ibox31 k).hi := by decide +kernel
private theorem accepted_31 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox31) tree31 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox31 midpoint_even_31
  simp only [tree31,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox31,candidate_valid h (FixedTape.midBox ibox31),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox31 113 (FixedTape.rowsAux denominator ibox31 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox31) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_31
private noncomputable def tree30 : TapeTree := .split 1 (((27678455799524133564663854349885341226998005727535746581868912053950873600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree31 tree32
attribute [irreducible] tree30
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox30 1 (27678455799524133564663854349885341226998005727535746581868912053950873600000000000000000000000 : Int) false,decode_split denominator ibox30 1 (27678455799524133564663854349885341226998005727535746581868912053950873600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_31 h,accepted_32 h⟩
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
private noncomputable def tree28 : TapeTree := .split 1 (((25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree29 tree30
attribute [irreducible] tree28
private theorem accepted_28 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox28) tree28 = true := by
  simp only [tree28,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox28 1 (25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) false,decode_split denominator ibox28 1 (25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) true]
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
private noncomputable def tree25 : TapeTree := .split 1 (((25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree26 tree27
attribute [irreducible] tree25
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox25 1 (25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) false,decode_split denominator ibox25 1 (25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_26 h,accepted_27 h⟩
private noncomputable def tree24 : TapeTree := .split 2 (((5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree25 tree28
attribute [irreducible] tree24
private theorem accepted_24 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox24) tree24 = true := by
  simp only [tree24,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox24 2 (5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 : Int) false,decode_split denominator ibox24 2 (5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_25 h,accepted_28 h⟩
private noncomputable def tree23 : TapeTree := .split 1 (((30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree24 tree33
attribute [irreducible] tree23
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox23 1 (30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) false,decode_split denominator ibox23 1 (30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_24 h,accepted_33 h⟩
private noncomputable def tree22 : TapeTree := .split 2 (((10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree23 tree101
attribute [irreducible] tree22
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox22 2 (10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) false,decode_split denominator ibox22 2 (10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_23 h,accepted_101 h⟩
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
private noncomputable def tree19 : TapeTree := .split 1 (((15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree21
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 1 (15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) false,decode_split denominator ibox19 1 (15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) true]
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
private noncomputable def tree16 : TapeTree := .split 1 (((15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree18
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 1 (15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) false,decode_split denominator ibox16 1 (15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_17 h,accepted_18 h⟩
private noncomputable def tree15 : TapeTree := .split 2 (((15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree16 tree19
attribute [irreducible] tree15
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox15 2 (15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) false,decode_split denominator ibox15 2 (15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) true]
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
private noncomputable def tree12 : TapeTree := .split 2 (((17613562781515357722967907313563398962635094553886384188462034943423283200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree13 tree14
attribute [irreducible] tree12
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox12 2 (17613562781515357722967907313563398962635094553886384188462034943423283200000000000000000000000 : Int) false,decode_split denominator ibox12 2 (17613562781515357722967907313563398962635094553886384188462034943423283200000000000000000000000 : Int) true]
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
private noncomputable def tree10 : TapeTree := .split 2 (((15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree11 tree12
attribute [irreducible] tree10
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox10 2 (15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) false,decode_split denominator ibox10 2 (15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_11 h,accepted_12 h⟩
private noncomputable def tree9 : TapeTree := .split 1 (((10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree10 tree15
attribute [irreducible] tree9
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox9 1 (10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) false,decode_split denominator ibox9 1 (10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) true]
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
private noncomputable def tree6 : TapeTree := .split 2 (((5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree8
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 2 (5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 : Int) false,decode_split denominator ibox6 2 (5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 : Int) true]
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
private noncomputable def tree4 : TapeTree := .split 1 (((10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree6
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 1 (10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) false,decode_split denominator ibox4 1 (10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_6 h⟩
private noncomputable def tree3 : TapeTree := .split 2 (((10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree9
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 2 (10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) false,decode_split denominator ibox3 2 (10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_9 h⟩
private noncomputable def tree2 : TapeTree := .split 1 (((20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree22
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 1 (20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 : Int) false,decode_split denominator ibox2 1 (20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_22 h⟩
private noncomputable def tree1 : TapeTree := .split 2 (((20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree2 tree142
attribute [irreducible] tree1
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox1 2 (20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 : Int) false,decode_split denominator ibox1 2 (20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_2 h,accepted_142 h⟩
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
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (23/32 : ℚ) (3645833333333333/5000000000000000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 113 = e123 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (23/32 : ℚ) (3645833333333333/5000000000000000 : ℚ)) x → eval e123 x ≤ 0 := by
  have hb := h.child_4 tape 113 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell94_high_internal_top

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell94_high_internal_top
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((23/32 : ℚ) : ℝ) < p ∧ p ≤ ((3645833333333333/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 94 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 94 p)
    (hkb : ((3645833333333333/5000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((23/32 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : bStar < a), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell94_high_internal_top.cell_bound h.child_8 h.child_9 (Cell94_high_internal_top.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell94_high_internal_top
