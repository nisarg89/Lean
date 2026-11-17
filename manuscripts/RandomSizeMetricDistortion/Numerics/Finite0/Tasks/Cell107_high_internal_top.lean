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
namespace Cell107_high_internal_top
private noncomputable def qValues : Fin 2 → ℚ := ![(7279053639785813765345068142299479748/3942872418191526105388346490738092127 : ℚ),(-346547691959319396452500000000000000/3942872418191526105388346490738092127 : ℚ)]
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
    priceLambda 107 p = ((7279053639785813765345068142299479748/3942872418191526105388346490738092127 : ℝ)+(-346547691959319396452500000000000000/3942872418191526105388346490738092127 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell107,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 107 p = 0 := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell107,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e123 x = (x 0*(1-x 0))*(aPoint x+priceLambda 107 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 107 (x 0)*psiStar (rPoint x)+(cStar-aPoint x-eta (0 : Fin 9)*psiStar (aPoint x))-(cStar-capPoint x-eta (0 : Fin 9)*psiStar (capPoint x))) := by
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
    (hL : lambdaStar (x 0) = priceLambda 107 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 107 (x 0)) :
    (1)*eval e123 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_neg (not_le.mpr ha),if_neg (not_le.mpr hA),hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (4010416666666667/5000000000000000 : ℚ) (13/16 : ℚ)) x → eval e123 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((4010416666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((13/16 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 107 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 107 p)
    (hkb : ((13/16 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((4010416666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : bStar < a) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h7 (4010416666666667/5000000000000000 : ℚ) (13/16 : ℚ) bStar p a A r hpcell hkb hr.2 hap hcase hpA hAr
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 107 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 107 (x 0) := by simpa only [hxp] using hT
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
.const (7279053639785813765345068142299479748/3942872418191526105388346490738092127 : ℚ),
.const (-346547691959319396452500000000000000/3942872418191526105388346490738092127 : ℚ),
.mul 104 1,
.add 103 105,
.mul 1 10,
.add 8 38,
.neg 55,
.add 108 109,
.mul 110 107,
.mul 106 102,
.add 111 112]
private noncomputable def ssaQVals : Fin 15 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(-2840189/5000000 : ℚ),(113609/200000 : ℚ),(1085/4818 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ),(4818/3733 : ℚ),(145513/100000 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(7279053639785813765345068142299479748/3942872418191526105388346490738092127 : ℚ),(-346547691959319396452500000000000000/3942872418191526105388346490738092127 : ℚ)]
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
private noncomputable def denominator : Int := 187281914017959530947666462872690394029354790657914511448443569816836505600000000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨150215701868571719599735076626439150055475846519561866347925157151555043762904654455767040000000,152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000⟩,⟨0,187281914017959530947666462872690394029354790657914511448443569816836505600000000000000000000000⟩,⟨0,187281914017959530947666462872690394029354790657914511448443569816836505600000000000000000000000⟩,⟨0,187281914017959530947666462872690394029354790657914511448443569816836505600000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 3 true
private noncomputable def ibox2 : Fin 4 → FixedTape.I := splitI ibox1 2 93640957008979765473833231436345197014677395328957255724221784908418252800000000000000000000000 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 1 93640957008979765473833231436345197014677395328957255724221784908418252800000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 2 46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 1 46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox4 1 46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 true
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 1 70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox6 1 70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox3 2 46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox9 1 46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 false
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox10 2 70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 false
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox10 2 70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 true
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox9 1 46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 true
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox13 2 70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 false
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox13 2 70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 true
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox15 1 70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 false
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox15 1 70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 true
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox2 1 93640957008979765473833231436345197014677395328957255724221784908418252800000000000000000000000 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox18 2 46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 false
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 1 140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox20 1 117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 false
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox20 1 117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 true
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox22 2 23410239252244941368458307859086299253669348832239313931055446227104563200000000000000000000000 false
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox22 2 23410239252244941368458307859086299253669348832239313931055446227104563200000000000000000000000 true
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox19 1 140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 true
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox25 1 163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 false
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox26 2 23410239252244941368458307859086299253669348832239313931055446227104563200000000000000000000000 false
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox27 1 152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 false
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox27 1 152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 true
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox26 2 23410239252244941368458307859086299253669348832239313931055446227104563200000000000000000000000 true
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox30 1 152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 false
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox30 1 152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 true
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox32 0 151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 false
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox32 0 151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 true
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox25 1 163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 true
private noncomputable def ibox36 : Fin 4 → FixedTape.I := splitI ibox35 2 23410239252244941368458307859086299253669348832239313931055446227104563200000000000000000000000 false
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox36 1 175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 false
private noncomputable def ibox38 : Fin 4 → FixedTape.I := faceI ibox37 1 true
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox38 2 11705119626122470684229153929543149626834674416119656965527723113552281600000000000000000000000 false
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox38 2 11705119626122470684229153929543149626834674416119656965527723113552281600000000000000000000000 true
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox36 1 175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 true
private noncomputable def ibox42 : Fin 4 → FixedTape.I := faceI ibox41 1 true
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox42 2 11705119626122470684229153929543149626834674416119656965527723113552281600000000000000000000000 false
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox43 2 5852559813061235342114576964771574813417337208059828482763861556776140800000000000000000000000 false
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox44 0 151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 false
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox45 2 2926279906530617671057288482385787406708668604029914241381930778388070400000000000000000000000 false
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox46 0 150703415186326819423546057740844598828819576742060284898908967982711198022178490841825280000000 false
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox46 0 150703415186326819423546057740844598828819576742060284898908967982711198022178490841825280000000 true
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox45 2 2926279906530617671057288482385787406708668604029914241381930778388070400000000000000000000000 true
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox44 0 151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 true
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox50 2 2926279906530617671057288482385787406708668604029914241381930778388070400000000000000000000000 false
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox51 0 151678841821837019071168019969655496375507037187057122000876589645023506540726163613941760000000 false
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox51 0 151678841821837019071168019969655496375507037187057122000876589645023506540726163613941760000000 true
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox50 2 2926279906530617671057288482385787406708668604029914241381930778388070400000000000000000000000 true
private noncomputable def ibox55 : Fin 4 → FixedTape.I := splitI ibox43 2 5852559813061235342114576964771574813417337208059828482763861556776140800000000000000000000000 true
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox55 0 151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 false
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox56 2 8778839719591853013171865447157362220126005812089742724145792335164211200000000000000000000000 false
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox56 2 8778839719591853013171865447157362220126005812089742724145792335164211200000000000000000000000 true
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox55 0 151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 true
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox42 2 11705119626122470684229153929543149626834674416119656965527723113552281600000000000000000000000 true
private noncomputable def ibox61 : Fin 4 → FixedTape.I := splitI ibox60 2 17557679439183706026343730894314724440252011624179485448291584670328422400000000000000000000000 false
private noncomputable def ibox62 : Fin 4 → FixedTape.I := splitI ibox61 0 151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 false
private noncomputable def ibox63 : Fin 4 → FixedTape.I := splitI ibox61 0 151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 true
private noncomputable def ibox64 : Fin 4 → FixedTape.I := splitI ibox60 2 17557679439183706026343730894314724440252011624179485448291584670328422400000000000000000000000 true
private noncomputable def ibox65 : Fin 4 → FixedTape.I := splitI ibox64 0 151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 false
private noncomputable def ibox66 : Fin 4 → FixedTape.I := splitI ibox64 0 151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 true
private noncomputable def ibox67 : Fin 4 → FixedTape.I := splitI ibox35 2 23410239252244941368458307859086299253669348832239313931055446227104563200000000000000000000000 true
private noncomputable def ibox68 : Fin 4 → FixedTape.I := splitI ibox67 1 175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 false
private noncomputable def ibox69 : Fin 4 → FixedTape.I := splitI ibox68 2 35115358878367412052687461788629448880504023248358970896583169340656844800000000000000000000000 false
private noncomputable def ibox70 : Fin 4 → FixedTape.I := splitI ibox69 1 169724234578775824921322731978375669589102779033735026000151985146508083200000000000000000000000 false
private noncomputable def ibox71 : Fin 4 → FixedTape.I := splitI ibox69 1 169724234578775824921322731978375669589102779033735026000151985146508083200000000000000000000000 true
private noncomputable def ibox72 : Fin 4 → FixedTape.I := splitI ibox68 2 35115358878367412052687461788629448880504023248358970896583169340656844800000000000000000000000 true
private noncomputable def ibox73 : Fin 4 → FixedTape.I := splitI ibox67 1 175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 true
private noncomputable def ibox74 : Fin 4 → FixedTape.I := splitI ibox73 2 35115358878367412052687461788629448880504023248358970896583169340656844800000000000000000000000 false
private noncomputable def ibox75 : Fin 4 → FixedTape.I := splitI ibox74 1 181429354204898295605551885907918819215937453449854682965679708260060364800000000000000000000000 false
private noncomputable def ibox76 : Fin 4 → FixedTape.I := faceI ibox75 1 true
private noncomputable def ibox77 : Fin 4 → FixedTape.I := splitI ibox74 1 181429354204898295605551885907918819215937453449854682965679708260060364800000000000000000000000 true
private noncomputable def ibox78 : Fin 4 → FixedTape.I := faceI ibox77 1 true
private noncomputable def ibox79 : Fin 4 → FixedTape.I := splitI ibox78 2 29262799065306176710572884823857874067086686040299142413819307783880704000000000000000000000000 false
private noncomputable def ibox80 : Fin 4 → FixedTape.I := splitI ibox78 2 29262799065306176710572884823857874067086686040299142413819307783880704000000000000000000000000 true
private noncomputable def ibox81 : Fin 4 → FixedTape.I := splitI ibox73 2 35115358878367412052687461788629448880504023248358970896583169340656844800000000000000000000000 true
private noncomputable def ibox82 : Fin 4 → FixedTape.I := splitI ibox81 1 181429354204898295605551885907918819215937453449854682965679708260060364800000000000000000000000 false
private noncomputable def ibox83 : Fin 4 → FixedTape.I := splitI ibox82 0 151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 false
private noncomputable def ibox84 : Fin 4 → FixedTape.I := splitI ibox82 0 151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 true
private noncomputable def ibox85 : Fin 4 → FixedTape.I := splitI ibox81 1 181429354204898295605551885907918819215937453449854682965679708260060364800000000000000000000000 true
private noncomputable def ibox86 : Fin 4 → FixedTape.I := splitI ibox85 0 151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 false
private noncomputable def ibox87 : Fin 4 → FixedTape.I := splitI ibox85 0 151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 true
private noncomputable def ibox88 : Fin 4 → FixedTape.I := splitI ibox18 2 46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 true
private noncomputable def ibox89 : Fin 4 → FixedTape.I := splitI ibox88 1 140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 false
private noncomputable def ibox90 : Fin 4 → FixedTape.I := splitI ibox89 2 70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 false
private noncomputable def ibox91 : Fin 4 → FixedTape.I := splitI ibox90 1 117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 false
private noncomputable def ibox92 : Fin 4 → FixedTape.I := splitI ibox90 1 117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 true
private noncomputable def ibox93 : Fin 4 → FixedTape.I := splitI ibox89 2 70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 true
private noncomputable def ibox94 : Fin 4 → FixedTape.I := splitI ibox93 1 117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 false
private noncomputable def ibox95 : Fin 4 → FixedTape.I := splitI ibox93 1 117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 true
private noncomputable def ibox96 : Fin 4 → FixedTape.I := splitI ibox95 2 81935837382857294789604077506802047387842720912837598758694061794865971200000000000000000000000 false
private noncomputable def ibox97 : Fin 4 → FixedTape.I := splitI ibox95 2 81935837382857294789604077506802047387842720912837598758694061794865971200000000000000000000000 true
private noncomputable def ibox98 : Fin 4 → FixedTape.I := splitI ibox88 1 140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 true
private noncomputable def ibox99 : Fin 4 → FixedTape.I := splitI ibox98 2 70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 false
private noncomputable def ibox100 : Fin 4 → FixedTape.I := splitI ibox99 1 163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 false
private noncomputable def ibox101 : Fin 4 → FixedTape.I := splitI ibox100 1 152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 false
private noncomputable def ibox102 : Fin 4 → FixedTape.I := splitI ibox100 1 152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 true
private noncomputable def ibox103 : Fin 4 → FixedTape.I := splitI ibox102 2 58525598130612353421145769647715748134173372080598284827638615567761408000000000000000000000000 false
private noncomputable def ibox104 : Fin 4 → FixedTape.I := splitI ibox102 2 58525598130612353421145769647715748134173372080598284827638615567761408000000000000000000000000 true
private noncomputable def ibox105 : Fin 4 → FixedTape.I := splitI ibox99 1 163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 true
private noncomputable def ibox106 : Fin 4 → FixedTape.I := splitI ibox105 2 58525598130612353421145769647715748134173372080598284827638615567761408000000000000000000000000 false
private noncomputable def ibox107 : Fin 4 → FixedTape.I := splitI ibox106 1 175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 false
private noncomputable def ibox108 : Fin 4 → FixedTape.I := splitI ibox106 1 175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 true
private noncomputable def ibox109 : Fin 4 → FixedTape.I := splitI ibox108 0 151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 false
private noncomputable def ibox110 : Fin 4 → FixedTape.I := splitI ibox108 0 151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 true
private noncomputable def ibox111 : Fin 4 → FixedTape.I := splitI ibox105 2 58525598130612353421145769647715748134173372080598284827638615567761408000000000000000000000000 true
private noncomputable def ibox112 : Fin 4 → FixedTape.I := splitI ibox111 1 175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 false
private noncomputable def ibox113 : Fin 4 → FixedTape.I := splitI ibox111 1 175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 true
private noncomputable def ibox114 : Fin 4 → FixedTape.I := splitI ibox113 0 151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 false
private noncomputable def ibox115 : Fin 4 → FixedTape.I := splitI ibox113 0 151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 true
private noncomputable def ibox116 : Fin 4 → FixedTape.I := splitI ibox98 2 70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 true
private noncomputable def ibox117 : Fin 4 → FixedTape.I := splitI ibox116 1 163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 false
private noncomputable def ibox118 : Fin 4 → FixedTape.I := splitI ibox117 2 81935837382857294789604077506802047387842720912837598758694061794865971200000000000000000000000 false
private noncomputable def ibox119 : Fin 4 → FixedTape.I := splitI ibox117 2 81935837382857294789604077506802047387842720912837598758694061794865971200000000000000000000000 true
private noncomputable def ibox120 : Fin 4 → FixedTape.I := splitI ibox116 1 163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 true
private noncomputable def ibox121 : Fin 4 → FixedTape.I := splitI ibox120 2 81935837382857294789604077506802047387842720912837598758694061794865971200000000000000000000000 false
private noncomputable def ibox122 : Fin 4 → FixedTape.I := splitI ibox121 1 175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 false
private noncomputable def ibox123 : Fin 4 → FixedTape.I := splitI ibox121 1 175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 true
private noncomputable def ibox124 : Fin 4 → FixedTape.I := splitI ibox120 2 81935837382857294789604077506802047387842720912837598758694061794865971200000000000000000000000 true
private noncomputable def ibox125 : Fin 4 → FixedTape.I := splitI ibox124 1 175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 false
private noncomputable def ibox126 : Fin 4 → FixedTape.I := splitI ibox124 1 175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 true
private noncomputable def ibox127 : Fin 4 → FixedTape.I := splitI ibox1 2 93640957008979765473833231436345197014677395328957255724221784908418252800000000000000000000000 true
private noncomputable def ibox128 : Fin 4 → FixedTape.I := splitI ibox127 2 140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 false
private noncomputable def ibox129 : Fin 4 → FixedTape.I := splitI ibox128 1 93640957008979765473833231436345197014677395328957255724221784908418252800000000000000000000000 false
private noncomputable def ibox130 : Fin 4 → FixedTape.I := splitI ibox129 2 117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 false
private noncomputable def ibox131 : Fin 4 → FixedTape.I := splitI ibox130 1 46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 false
private noncomputable def ibox132 : Fin 4 → FixedTape.I := splitI ibox131 2 105346076635102236158062385365888346641512069745076912689749508021970534400000000000000000000000 false
private noncomputable def ibox133 : Fin 4 → FixedTape.I := splitI ibox131 2 105346076635102236158062385365888346641512069745076912689749508021970534400000000000000000000000 true
private noncomputable def ibox134 : Fin 4 → FixedTape.I := splitI ibox130 1 46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 true
private noncomputable def ibox135 : Fin 4 → FixedTape.I := splitI ibox134 2 105346076635102236158062385365888346641512069745076912689749508021970534400000000000000000000000 false
private noncomputable def ibox136 : Fin 4 → FixedTape.I := splitI ibox134 2 105346076635102236158062385365888346641512069745076912689749508021970534400000000000000000000000 true
private noncomputable def ibox137 : Fin 4 → FixedTape.I := splitI ibox129 2 117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 true
private noncomputable def ibox138 : Fin 4 → FixedTape.I := splitI ibox137 1 46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 false
private noncomputable def ibox139 : Fin 4 → FixedTape.I := splitI ibox138 2 128756315887347177526520693224974645895181418577316226620804954249075097600000000000000000000000 false
private noncomputable def ibox140 : Fin 4 → FixedTape.I := splitI ibox138 2 128756315887347177526520693224974645895181418577316226620804954249075097600000000000000000000000 true
private noncomputable def ibox141 : Fin 4 → FixedTape.I := splitI ibox137 1 46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 true
private noncomputable def ibox142 : Fin 4 → FixedTape.I := splitI ibox141 2 128756315887347177526520693224974645895181418577316226620804954249075097600000000000000000000000 false
private noncomputable def ibox143 : Fin 4 → FixedTape.I := splitI ibox141 2 128756315887347177526520693224974645895181418577316226620804954249075097600000000000000000000000 true
private noncomputable def ibox144 : Fin 4 → FixedTape.I := splitI ibox128 1 93640957008979765473833231436345197014677395328957255724221784908418252800000000000000000000000 true
private noncomputable def ibox145 : Fin 4 → FixedTape.I := splitI ibox144 2 117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 false
private noncomputable def ibox146 : Fin 4 → FixedTape.I := splitI ibox145 1 140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 false
private noncomputable def ibox147 : Fin 4 → FixedTape.I := splitI ibox146 2 105346076635102236158062385365888346641512069745076912689749508021970534400000000000000000000000 false
private noncomputable def ibox148 : Fin 4 → FixedTape.I := splitI ibox147 1 117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 false
private noncomputable def ibox149 : Fin 4 → FixedTape.I := splitI ibox147 1 117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 true
private noncomputable def ibox150 : Fin 4 → FixedTape.I := splitI ibox146 2 105346076635102236158062385365888346641512069745076912689749508021970534400000000000000000000000 true
private noncomputable def ibox151 : Fin 4 → FixedTape.I := splitI ibox150 1 117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 false
private noncomputable def ibox152 : Fin 4 → FixedTape.I := splitI ibox150 1 117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 true
private noncomputable def ibox153 : Fin 4 → FixedTape.I := splitI ibox145 1 140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 true
private noncomputable def ibox154 : Fin 4 → FixedTape.I := splitI ibox153 2 105346076635102236158062385365888346641512069745076912689749508021970534400000000000000000000000 false
private noncomputable def ibox155 : Fin 4 → FixedTape.I := splitI ibox154 1 163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 false
private noncomputable def ibox156 : Fin 4 → FixedTape.I := splitI ibox154 1 163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 true
private noncomputable def ibox157 : Fin 4 → FixedTape.I := splitI ibox156 2 99493516822041000815947808401116771828094732537017084206985646465194393600000000000000000000000 false
private noncomputable def ibox158 : Fin 4 → FixedTape.I := splitI ibox156 2 99493516822041000815947808401116771828094732537017084206985646465194393600000000000000000000000 true
private noncomputable def ibox159 : Fin 4 → FixedTape.I := splitI ibox153 2 105346076635102236158062385365888346641512069745076912689749508021970534400000000000000000000000 true
private noncomputable def ibox160 : Fin 4 → FixedTape.I := splitI ibox159 1 163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 false
private noncomputable def ibox161 : Fin 4 → FixedTape.I := splitI ibox159 1 163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 true
private noncomputable def ibox162 : Fin 4 → FixedTape.I := splitI ibox161 2 111198636448163471500176962330659921454929406953136741172513369578746675200000000000000000000000 false
private noncomputable def ibox163 : Fin 4 → FixedTape.I := splitI ibox161 2 111198636448163471500176962330659921454929406953136741172513369578746675200000000000000000000000 true
private noncomputable def ibox164 : Fin 4 → FixedTape.I := splitI ibox144 2 117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 true
private noncomputable def ibox165 : Fin 4 → FixedTape.I := splitI ibox164 1 140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 false
private noncomputable def ibox166 : Fin 4 → FixedTape.I := splitI ibox165 2 128756315887347177526520693224974645895181418577316226620804954249075097600000000000000000000000 false
private noncomputable def ibox167 : Fin 4 → FixedTape.I := splitI ibox166 1 117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 false
private noncomputable def ibox168 : Fin 4 → FixedTape.I := splitI ibox166 1 117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 true
private noncomputable def ibox169 : Fin 4 → FixedTape.I := splitI ibox165 2 128756315887347177526520693224974645895181418577316226620804954249075097600000000000000000000000 true
private noncomputable def ibox170 : Fin 4 → FixedTape.I := splitI ibox164 1 140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 true
private noncomputable def ibox171 : Fin 4 → FixedTape.I := splitI ibox170 2 128756315887347177526520693224974645895181418577316226620804954249075097600000000000000000000000 false
private noncomputable def ibox172 : Fin 4 → FixedTape.I := splitI ibox171 1 163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 false
private noncomputable def ibox173 : Fin 4 → FixedTape.I := splitI ibox171 1 163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 true
private noncomputable def ibox174 : Fin 4 → FixedTape.I := splitI ibox170 2 128756315887347177526520693224974645895181418577316226620804954249075097600000000000000000000000 true
private noncomputable def ibox175 : Fin 4 → FixedTape.I := splitI ibox174 1 163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 false
private noncomputable def ibox176 : Fin 4 → FixedTape.I := splitI ibox174 1 163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 true
private noncomputable def ibox177 : Fin 4 → FixedTape.I := splitI ibox127 2 140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 true
private noncomputable def ibox178 : Fin 4 → FixedTape.I := splitI ibox177 1 93640957008979765473833231436345197014677395328957255724221784908418252800000000000000000000000 false
private noncomputable def ibox179 : Fin 4 → FixedTape.I := splitI ibox178 2 163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 false
private noncomputable def ibox180 : Fin 4 → FixedTape.I := splitI ibox179 2 152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 false
private noncomputable def ibox181 : Fin 4 → FixedTape.I := splitI ibox180 1 46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 false
private noncomputable def ibox182 : Fin 4 → FixedTape.I := splitI ibox180 1 46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 true
private noncomputable def ibox183 : Fin 4 → FixedTape.I := splitI ibox179 2 152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 true
private noncomputable def ibox184 : Fin 4 → FixedTape.I := splitI ibox183 1 46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 false
private noncomputable def ibox185 : Fin 4 → FixedTape.I := splitI ibox183 1 46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 true
private noncomputable def ibox186 : Fin 4 → FixedTape.I := splitI ibox178 2 163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 true
private noncomputable def ibox187 : Fin 4 → FixedTape.I := splitI ibox186 2 175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 false
private noncomputable def ibox188 : Fin 4 → FixedTape.I := splitI ibox187 2 169724234578775824921322731978375669589102779033735026000151985146508083200000000000000000000000 false
private noncomputable def ibox189 : Fin 4 → FixedTape.I := splitI ibox187 2 169724234578775824921322731978375669589102779033735026000151985146508083200000000000000000000000 true
private noncomputable def ibox190 : Fin 4 → FixedTape.I := splitI ibox186 2 175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 true
private noncomputable def ibox191 : Fin 4 → FixedTape.I := splitI ibox177 1 93640957008979765473833231436345197014677395328957255724221784908418252800000000000000000000000 true
private noncomputable def ibox192 : Fin 4 → FixedTape.I := splitI ibox191 2 163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 false
private noncomputable def ibox193 : Fin 4 → FixedTape.I := splitI ibox192 1 140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 false
private noncomputable def ibox194 : Fin 4 → FixedTape.I := splitI ibox193 2 152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 false
private noncomputable def ibox195 : Fin 4 → FixedTape.I := splitI ibox193 2 152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 true
private noncomputable def ibox196 : Fin 4 → FixedTape.I := splitI ibox192 1 140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 true
private noncomputable def ibox197 : Fin 4 → FixedTape.I := splitI ibox196 2 152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 false
private noncomputable def ibox198 : Fin 4 → FixedTape.I := faceI ibox197 2 false
private noncomputable def ibox199 : Fin 4 → FixedTape.I := splitI ibox196 2 152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 true
private noncomputable def ibox200 : Fin 4 → FixedTape.I := faceI ibox199 2 false
private noncomputable def ibox201 : Fin 4 → FixedTape.I := splitI ibox191 2 163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 true
private noncomputable def ibox202 : Fin 4 → FixedTape.I := splitI ibox201 1 140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 false
private noncomputable def ibox203 : Fin 4 → FixedTape.I := splitI ibox202 2 175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 false
private noncomputable def ibox204 : Fin 4 → FixedTape.I := splitI ibox202 2 175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 true
private noncomputable def ibox205 : Fin 4 → FixedTape.I := splitI ibox201 1 140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 true
private noncomputable def ibox206 : Fin 4 → FixedTape.I := splitI ibox205 2 175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 false
private noncomputable def ibox207 : Fin 4 → FixedTape.I := faceI ibox206 2 false
private noncomputable def ibox208 : Fin 4 → FixedTape.I := splitI ibox205 2 175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 true
private noncomputable def ibox209 : Fin 4 → FixedTape.I := faceI ibox208 2 false
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
private noncomputable def tree208 : TapeTree := .face 2 false (candidateRows ibox208) tree209
attribute [irreducible] tree208
private theorem sign_208 : ((computed denominator ibox208).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_208 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox208) tree208 = true := by
  simp only [tree208,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox208,?_,accepted_209 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox208)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox208).gradient 2).hi) denominator_positive).1 sign_208
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
private noncomputable def tree206 : TapeTree := .face 2 false (candidateRows ibox206) tree207
attribute [irreducible] tree206
private theorem sign_206 : ((computed denominator ibox206).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_206 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox206) tree206 = true := by
  simp only [tree206,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox206,?_,accepted_207 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox206)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox206).gradient 2).hi) denominator_positive).1 sign_206
private noncomputable def tree205 : TapeTree := .split 2 (((175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree206 tree208
attribute [irreducible] tree205
private theorem accepted_205 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox205) tree205 = true := by
  simp only [tree205,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox205 2 (175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) false,decode_split denominator ibox205 2 (175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_206 h,accepted_208 h⟩
private noncomputable def tree204 : TapeTree := .centered (candidateRows ibox204) (candidateRows (FixedTape.midBox ibox204))
attribute [irreducible] tree204
private theorem sign_204 : 2*denominator*(computed denominator (FixedTape.midBox ibox204)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox204).gradient k).lo.natAbs ((computed denominator ibox204).gradient k).hi.natAbs : Int)*((ibox204 k).hi-(ibox204 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox204
    (computed denominator ibox204) (computed denominator (FixedTape.midBox ibox204))
    (by decide +kernel)
private theorem midpoint_even_204 : ∀ k, 2 ∣ (ibox204 k).lo+(ibox204 k).hi := by decide +kernel
private theorem accepted_204 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox204) tree204 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox204 midpoint_even_204
  simp only [tree204,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox204,candidate_valid h (FixedTape.midBox ibox204),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox204 113 (FixedTape.rowsAux denominator ibox204 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox204) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_204
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
private noncomputable def tree202 : TapeTree := .split 2 (((175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree203 tree204
attribute [irreducible] tree202
private theorem accepted_202 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox202) tree202 = true := by
  simp only [tree202,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox202 2 (175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) false,decode_split denominator ibox202 2 (175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_203 h,accepted_204 h⟩
private noncomputable def tree201 : TapeTree := .split 1 (((140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree202 tree205
attribute [irreducible] tree201
private theorem accepted_201 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox201) tree201 = true := by
  simp only [tree201,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox201 1 (140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) false,decode_split denominator ibox201 1 (140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_202 h,accepted_205 h⟩
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
private noncomputable def tree199 : TapeTree := .face 2 false (candidateRows ibox199) tree200
attribute [irreducible] tree199
private theorem sign_199 : ((computed denominator ibox199).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_199 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox199) tree199 = true := by
  simp only [tree199,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox199,?_,accepted_200 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox199)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox199).gradient 2).hi) denominator_positive).1 sign_199
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
private noncomputable def tree197 : TapeTree := .face 2 false (candidateRows ibox197) tree198
attribute [irreducible] tree197
private theorem sign_197 : ((computed denominator ibox197).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_197 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox197) tree197 = true := by
  simp only [tree197,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox197,?_,accepted_198 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox197)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox197).gradient 2).hi) denominator_positive).1 sign_197
private noncomputable def tree196 : TapeTree := .split 2 (((152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree197 tree199
attribute [irreducible] tree196
private theorem accepted_196 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox196) tree196 = true := by
  simp only [tree196,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox196 2 (152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 : Int) false,decode_split denominator ibox196 2 (152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_197 h,accepted_199 h⟩
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
private noncomputable def tree193 : TapeTree := .split 2 (((152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree194 tree195
attribute [irreducible] tree193
private theorem accepted_193 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox193) tree193 = true := by
  simp only [tree193,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox193 2 (152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 : Int) false,decode_split denominator ibox193 2 (152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_194 h,accepted_195 h⟩
private noncomputable def tree192 : TapeTree := .split 1 (((140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree193 tree196
attribute [irreducible] tree192
private theorem accepted_192 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox192) tree192 = true := by
  simp only [tree192,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox192 1 (140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) false,decode_split denominator ibox192 1 (140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_193 h,accepted_196 h⟩
private noncomputable def tree191 : TapeTree := .split 2 (((163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree192 tree201
attribute [irreducible] tree191
private theorem accepted_191 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox191) tree191 = true := by
  simp only [tree191,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox191 2 (163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) false,decode_split denominator ibox191 2 (163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_192 h,accepted_201 h⟩
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
private noncomputable def tree188 : TapeTree := .centered (candidateRows ibox188) (candidateRows (FixedTape.midBox ibox188))
attribute [irreducible] tree188
private theorem sign_188 : 2*denominator*(computed denominator (FixedTape.midBox ibox188)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox188).gradient k).lo.natAbs ((computed denominator ibox188).gradient k).hi.natAbs : Int)*((ibox188 k).hi-(ibox188 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox188
    (computed denominator ibox188) (computed denominator (FixedTape.midBox ibox188))
    (by decide +kernel)
private theorem midpoint_even_188 : ∀ k, 2 ∣ (ibox188 k).lo+(ibox188 k).hi := by decide +kernel
private theorem accepted_188 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox188) tree188 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox188 midpoint_even_188
  simp only [tree188,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox188,candidate_valid h (FixedTape.midBox ibox188),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox188 113 (FixedTape.rowsAux denominator ibox188 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox188) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_188
private noncomputable def tree187 : TapeTree := .split 2 (((169724234578775824921322731978375669589102779033735026000151985146508083200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree188 tree189
attribute [irreducible] tree187
private theorem accepted_187 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox187) tree187 = true := by
  simp only [tree187,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox187 2 (169724234578775824921322731978375669589102779033735026000151985146508083200000000000000000000000 : Int) false,decode_split denominator ibox187 2 (169724234578775824921322731978375669589102779033735026000151985146508083200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_188 h,accepted_189 h⟩
private noncomputable def tree186 : TapeTree := .split 2 (((175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree187 tree190
attribute [irreducible] tree186
private theorem accepted_186 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox186) tree186 = true := by
  simp only [tree186,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox186 2 (175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) false,decode_split denominator ibox186 2 (175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_187 h,accepted_190 h⟩
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
private noncomputable def tree184 : TapeTree := .centered (candidateRows ibox184) (candidateRows (FixedTape.midBox ibox184))
attribute [irreducible] tree184
private theorem sign_184 : 2*denominator*(computed denominator (FixedTape.midBox ibox184)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox184).gradient k).lo.natAbs ((computed denominator ibox184).gradient k).hi.natAbs : Int)*((ibox184 k).hi-(ibox184 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox184
    (computed denominator ibox184) (computed denominator (FixedTape.midBox ibox184))
    (by decide +kernel)
private theorem midpoint_even_184 : ∀ k, 2 ∣ (ibox184 k).lo+(ibox184 k).hi := by decide +kernel
private theorem accepted_184 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox184) tree184 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox184 midpoint_even_184
  simp only [tree184,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox184,candidate_valid h (FixedTape.midBox ibox184),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox184 113 (FixedTape.rowsAux denominator ibox184 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox184) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_184
private noncomputable def tree183 : TapeTree := .split 1 (((46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree184 tree185
attribute [irreducible] tree183
private theorem accepted_183 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox183) tree183 = true := by
  simp only [tree183,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox183 1 (46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) false,decode_split denominator ibox183 1 (46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_184 h,accepted_185 h⟩
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
private noncomputable def tree181 : TapeTree := .centered (candidateRows ibox181) (candidateRows (FixedTape.midBox ibox181))
attribute [irreducible] tree181
private theorem sign_181 : 2*denominator*(computed denominator (FixedTape.midBox ibox181)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox181).gradient k).lo.natAbs ((computed denominator ibox181).gradient k).hi.natAbs : Int)*((ibox181 k).hi-(ibox181 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox181
    (computed denominator ibox181) (computed denominator (FixedTape.midBox ibox181))
    (by decide +kernel)
private theorem midpoint_even_181 : ∀ k, 2 ∣ (ibox181 k).lo+(ibox181 k).hi := by decide +kernel
private theorem accepted_181 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox181) tree181 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox181 midpoint_even_181
  simp only [tree181,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox181,candidate_valid h (FixedTape.midBox ibox181),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox181 113 (FixedTape.rowsAux denominator ibox181 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox181) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_181
private noncomputable def tree180 : TapeTree := .split 1 (((46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree181 tree182
attribute [irreducible] tree180
private theorem accepted_180 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox180) tree180 = true := by
  simp only [tree180,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox180 1 (46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) false,decode_split denominator ibox180 1 (46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_181 h,accepted_182 h⟩
private noncomputable def tree179 : TapeTree := .split 2 (((152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree180 tree183
attribute [irreducible] tree179
private theorem accepted_179 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox179) tree179 = true := by
  simp only [tree179,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox179 2 (152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 : Int) false,decode_split denominator ibox179 2 (152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_180 h,accepted_183 h⟩
private noncomputable def tree178 : TapeTree := .split 2 (((163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree179 tree186
attribute [irreducible] tree178
private theorem accepted_178 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox178) tree178 = true := by
  simp only [tree178,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox178 2 (163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) false,decode_split denominator ibox178 2 (163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_179 h,accepted_186 h⟩
private noncomputable def tree177 : TapeTree := .split 1 (((93640957008979765473833231436345197014677395328957255724221784908418252800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree178 tree191
attribute [irreducible] tree177
private theorem accepted_177 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox177) tree177 = true := by
  simp only [tree177,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox177 1 (93640957008979765473833231436345197014677395328957255724221784908418252800000000000000000000000 : Int) false,decode_split denominator ibox177 1 (93640957008979765473833231436345197014677395328957255724221784908418252800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_178 h,accepted_191 h⟩
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
private noncomputable def tree174 : TapeTree := .split 1 (((163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree175 tree176
attribute [irreducible] tree174
private theorem accepted_174 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox174) tree174 = true := by
  simp only [tree174,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox174 1 (163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) false,decode_split denominator ibox174 1 (163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_175 h,accepted_176 h⟩
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
private noncomputable def tree172 : TapeTree := .centered (candidateRows ibox172) (candidateRows (FixedTape.midBox ibox172))
attribute [irreducible] tree172
private theorem sign_172 : 2*denominator*(computed denominator (FixedTape.midBox ibox172)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox172).gradient k).lo.natAbs ((computed denominator ibox172).gradient k).hi.natAbs : Int)*((ibox172 k).hi-(ibox172 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox172
    (computed denominator ibox172) (computed denominator (FixedTape.midBox ibox172))
    (by decide +kernel)
private theorem midpoint_even_172 : ∀ k, 2 ∣ (ibox172 k).lo+(ibox172 k).hi := by decide +kernel
private theorem accepted_172 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox172) tree172 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox172 midpoint_even_172
  simp only [tree172,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox172,candidate_valid h (FixedTape.midBox ibox172),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox172 113 (FixedTape.rowsAux denominator ibox172 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox172) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_172
private noncomputable def tree171 : TapeTree := .split 1 (((163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree172 tree173
attribute [irreducible] tree171
private theorem accepted_171 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox171) tree171 = true := by
  simp only [tree171,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox171 1 (163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) false,decode_split denominator ibox171 1 (163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_172 h,accepted_173 h⟩
private noncomputable def tree170 : TapeTree := .split 2 (((128756315887347177526520693224974645895181418577316226620804954249075097600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree171 tree174
attribute [irreducible] tree170
private theorem accepted_170 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox170) tree170 = true := by
  simp only [tree170,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox170 2 (128756315887347177526520693224974645895181418577316226620804954249075097600000000000000000000000 : Int) false,decode_split denominator ibox170 2 (128756315887347177526520693224974645895181418577316226620804954249075097600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_171 h,accepted_174 h⟩
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
private noncomputable def tree168 : TapeTree := .centered (candidateRows ibox168) (candidateRows (FixedTape.midBox ibox168))
attribute [irreducible] tree168
private theorem sign_168 : 2*denominator*(computed denominator (FixedTape.midBox ibox168)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox168).gradient k).lo.natAbs ((computed denominator ibox168).gradient k).hi.natAbs : Int)*((ibox168 k).hi-(ibox168 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox168
    (computed denominator ibox168) (computed denominator (FixedTape.midBox ibox168))
    (by decide +kernel)
private theorem midpoint_even_168 : ∀ k, 2 ∣ (ibox168 k).lo+(ibox168 k).hi := by decide +kernel
private theorem accepted_168 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox168) tree168 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox168 midpoint_even_168
  simp only [tree168,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox168,candidate_valid h (FixedTape.midBox ibox168),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox168 113 (FixedTape.rowsAux denominator ibox168 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox168) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_168
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
private noncomputable def tree166 : TapeTree := .split 1 (((117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree167 tree168
attribute [irreducible] tree166
private theorem accepted_166 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox166) tree166 = true := by
  simp only [tree166,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox166 1 (117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) false,decode_split denominator ibox166 1 (117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_167 h,accepted_168 h⟩
private noncomputable def tree165 : TapeTree := .split 2 (((128756315887347177526520693224974645895181418577316226620804954249075097600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree166 tree169
attribute [irreducible] tree165
private theorem accepted_165 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox165) tree165 = true := by
  simp only [tree165,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox165 2 (128756315887347177526520693224974645895181418577316226620804954249075097600000000000000000000000 : Int) false,decode_split denominator ibox165 2 (128756315887347177526520693224974645895181418577316226620804954249075097600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_166 h,accepted_169 h⟩
private noncomputable def tree164 : TapeTree := .split 1 (((140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree165 tree170
attribute [irreducible] tree164
private theorem accepted_164 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox164) tree164 = true := by
  simp only [tree164,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox164 1 (140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) false,decode_split denominator ibox164 1 (140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_165 h,accepted_170 h⟩
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
private noncomputable def tree161 : TapeTree := .split 2 (((111198636448163471500176962330659921454929406953136741172513369578746675200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree162 tree163
attribute [irreducible] tree161
private theorem accepted_161 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox161) tree161 = true := by
  simp only [tree161,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox161 2 (111198636448163471500176962330659921454929406953136741172513369578746675200000000000000000000000 : Int) false,decode_split denominator ibox161 2 (111198636448163471500176962330659921454929406953136741172513369578746675200000000000000000000000 : Int) true]
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
private noncomputable def tree159 : TapeTree := .split 1 (((163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree160 tree161
attribute [irreducible] tree159
private theorem accepted_159 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox159) tree159 = true := by
  simp only [tree159,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox159 1 (163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) false,decode_split denominator ibox159 1 (163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_160 h,accepted_161 h⟩
private noncomputable def tree158 : TapeTree := .centered (candidateRows ibox158) (candidateRows (FixedTape.midBox ibox158))
attribute [irreducible] tree158
private theorem sign_158 : 2*denominator*(computed denominator (FixedTape.midBox ibox158)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox158).gradient k).lo.natAbs ((computed denominator ibox158).gradient k).hi.natAbs : Int)*((ibox158 k).hi-(ibox158 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox158
    (computed denominator ibox158) (computed denominator (FixedTape.midBox ibox158))
    (by decide +kernel)
private theorem midpoint_even_158 : ∀ k, 2 ∣ (ibox158 k).lo+(ibox158 k).hi := by decide +kernel
private theorem accepted_158 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox158) tree158 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox158 midpoint_even_158
  simp only [tree158,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox158,candidate_valid h (FixedTape.midBox ibox158),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox158 113 (FixedTape.rowsAux denominator ibox158 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox158) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_158
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
private noncomputable def tree156 : TapeTree := .split 2 (((99493516822041000815947808401116771828094732537017084206985646465194393600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree157 tree158
attribute [irreducible] tree156
private theorem accepted_156 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox156) tree156 = true := by
  simp only [tree156,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox156 2 (99493516822041000815947808401116771828094732537017084206985646465194393600000000000000000000000 : Int) false,decode_split denominator ibox156 2 (99493516822041000815947808401116771828094732537017084206985646465194393600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_157 h,accepted_158 h⟩
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
private noncomputable def tree154 : TapeTree := .split 1 (((163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree155 tree156
attribute [irreducible] tree154
private theorem accepted_154 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox154) tree154 = true := by
  simp only [tree154,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox154 1 (163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) false,decode_split denominator ibox154 1 (163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_155 h,accepted_156 h⟩
private noncomputable def tree153 : TapeTree := .split 2 (((105346076635102236158062385365888346641512069745076912689749508021970534400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree154 tree159
attribute [irreducible] tree153
private theorem accepted_153 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox153) tree153 = true := by
  simp only [tree153,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox153 2 (105346076635102236158062385365888346641512069745076912689749508021970534400000000000000000000000 : Int) false,decode_split denominator ibox153 2 (105346076635102236158062385365888346641512069745076912689749508021970534400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_154 h,accepted_159 h⟩
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
private noncomputable def tree151 : TapeTree := .centered (candidateRows ibox151) (candidateRows (FixedTape.midBox ibox151))
attribute [irreducible] tree151
private theorem sign_151 : 2*denominator*(computed denominator (FixedTape.midBox ibox151)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox151).gradient k).lo.natAbs ((computed denominator ibox151).gradient k).hi.natAbs : Int)*((ibox151 k).hi-(ibox151 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox151
    (computed denominator ibox151) (computed denominator (FixedTape.midBox ibox151))
    (by decide +kernel)
private theorem midpoint_even_151 : ∀ k, 2 ∣ (ibox151 k).lo+(ibox151 k).hi := by decide +kernel
private theorem accepted_151 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox151) tree151 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox151 midpoint_even_151
  simp only [tree151,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox151,candidate_valid h (FixedTape.midBox ibox151),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox151 113 (FixedTape.rowsAux denominator ibox151 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox151) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_151
private noncomputable def tree150 : TapeTree := .split 1 (((117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree151 tree152
attribute [irreducible] tree150
private theorem accepted_150 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox150) tree150 = true := by
  simp only [tree150,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox150 1 (117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) false,decode_split denominator ibox150 1 (117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_151 h,accepted_152 h⟩
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
private noncomputable def tree148 : TapeTree := .centered (candidateRows ibox148) (candidateRows (FixedTape.midBox ibox148))
attribute [irreducible] tree148
private theorem sign_148 : 2*denominator*(computed denominator (FixedTape.midBox ibox148)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox148).gradient k).lo.natAbs ((computed denominator ibox148).gradient k).hi.natAbs : Int)*((ibox148 k).hi-(ibox148 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox148
    (computed denominator ibox148) (computed denominator (FixedTape.midBox ibox148))
    (by decide +kernel)
private theorem midpoint_even_148 : ∀ k, 2 ∣ (ibox148 k).lo+(ibox148 k).hi := by decide +kernel
private theorem accepted_148 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox148) tree148 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox148 midpoint_even_148
  simp only [tree148,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox148,candidate_valid h (FixedTape.midBox ibox148),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox148 113 (FixedTape.rowsAux denominator ibox148 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox148) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_148
private noncomputable def tree147 : TapeTree := .split 1 (((117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree148 tree149
attribute [irreducible] tree147
private theorem accepted_147 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox147) tree147 = true := by
  simp only [tree147,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox147 1 (117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) false,decode_split denominator ibox147 1 (117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_148 h,accepted_149 h⟩
private noncomputable def tree146 : TapeTree := .split 2 (((105346076635102236158062385365888346641512069745076912689749508021970534400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree147 tree150
attribute [irreducible] tree146
private theorem accepted_146 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox146) tree146 = true := by
  simp only [tree146,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox146 2 (105346076635102236158062385365888346641512069745076912689749508021970534400000000000000000000000 : Int) false,decode_split denominator ibox146 2 (105346076635102236158062385365888346641512069745076912689749508021970534400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_147 h,accepted_150 h⟩
private noncomputable def tree145 : TapeTree := .split 1 (((140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree146 tree153
attribute [irreducible] tree145
private theorem accepted_145 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox145) tree145 = true := by
  simp only [tree145,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox145 1 (140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) false,decode_split denominator ibox145 1 (140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_146 h,accepted_153 h⟩
private noncomputable def tree144 : TapeTree := .split 2 (((117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree145 tree164
attribute [irreducible] tree144
private theorem accepted_144 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox144) tree144 = true := by
  simp only [tree144,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox144 2 (117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) false,decode_split denominator ibox144 2 (117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_145 h,accepted_164 h⟩
private noncomputable def tree143 : TapeTree := .centered (candidateRows ibox143) (candidateRows (FixedTape.midBox ibox143))
attribute [irreducible] tree143
private theorem sign_143 : 2*denominator*(computed denominator (FixedTape.midBox ibox143)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox143).gradient k).lo.natAbs ((computed denominator ibox143).gradient k).hi.natAbs : Int)*((ibox143 k).hi-(ibox143 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox143
    (computed denominator ibox143) (computed denominator (FixedTape.midBox ibox143))
    (by decide +kernel)
private theorem midpoint_even_143 : ∀ k, 2 ∣ (ibox143 k).lo+(ibox143 k).hi := by decide +kernel
private theorem accepted_143 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox143) tree143 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox143 midpoint_even_143
  simp only [tree143,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox143,candidate_valid h (FixedTape.midBox ibox143),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox143 113 (FixedTape.rowsAux denominator ibox143 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox143) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_143
private noncomputable def tree142 : TapeTree := .centered (candidateRows ibox142) (candidateRows (FixedTape.midBox ibox142))
attribute [irreducible] tree142
private theorem sign_142 : 2*denominator*(computed denominator (FixedTape.midBox ibox142)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox142).gradient k).lo.natAbs ((computed denominator ibox142).gradient k).hi.natAbs : Int)*((ibox142 k).hi-(ibox142 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox142
    (computed denominator ibox142) (computed denominator (FixedTape.midBox ibox142))
    (by decide +kernel)
private theorem midpoint_even_142 : ∀ k, 2 ∣ (ibox142 k).lo+(ibox142 k).hi := by decide +kernel
private theorem accepted_142 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox142) tree142 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox142 midpoint_even_142
  simp only [tree142,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox142,candidate_valid h (FixedTape.midBox ibox142),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox142 113 (FixedTape.rowsAux denominator ibox142 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox142) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_142
private noncomputable def tree141 : TapeTree := .split 2 (((128756315887347177526520693224974645895181418577316226620804954249075097600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree142 tree143
attribute [irreducible] tree141
private theorem accepted_141 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox141) tree141 = true := by
  simp only [tree141,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox141 2 (128756315887347177526520693224974645895181418577316226620804954249075097600000000000000000000000 : Int) false,decode_split denominator ibox141 2 (128756315887347177526520693224974645895181418577316226620804954249075097600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_142 h,accepted_143 h⟩
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
private noncomputable def tree139 : TapeTree := .centered (candidateRows ibox139) (candidateRows (FixedTape.midBox ibox139))
attribute [irreducible] tree139
private theorem sign_139 : 2*denominator*(computed denominator (FixedTape.midBox ibox139)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox139).gradient k).lo.natAbs ((computed denominator ibox139).gradient k).hi.natAbs : Int)*((ibox139 k).hi-(ibox139 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox139
    (computed denominator ibox139) (computed denominator (FixedTape.midBox ibox139))
    (by decide +kernel)
private theorem midpoint_even_139 : ∀ k, 2 ∣ (ibox139 k).lo+(ibox139 k).hi := by decide +kernel
private theorem accepted_139 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox139) tree139 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox139 midpoint_even_139
  simp only [tree139,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox139,candidate_valid h (FixedTape.midBox ibox139),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox139 113 (FixedTape.rowsAux denominator ibox139 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox139) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_139
private noncomputable def tree138 : TapeTree := .split 2 (((128756315887347177526520693224974645895181418577316226620804954249075097600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree139 tree140
attribute [irreducible] tree138
private theorem accepted_138 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox138) tree138 = true := by
  simp only [tree138,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox138 2 (128756315887347177526520693224974645895181418577316226620804954249075097600000000000000000000000 : Int) false,decode_split denominator ibox138 2 (128756315887347177526520693224974645895181418577316226620804954249075097600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_139 h,accepted_140 h⟩
private noncomputable def tree137 : TapeTree := .split 1 (((46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree138 tree141
attribute [irreducible] tree137
private theorem accepted_137 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox137) tree137 = true := by
  simp only [tree137,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox137 1 (46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) false,decode_split denominator ibox137 1 (46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_138 h,accepted_141 h⟩
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
private noncomputable def tree135 : TapeTree := .centered (candidateRows ibox135) (candidateRows (FixedTape.midBox ibox135))
attribute [irreducible] tree135
private theorem sign_135 : 2*denominator*(computed denominator (FixedTape.midBox ibox135)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox135).gradient k).lo.natAbs ((computed denominator ibox135).gradient k).hi.natAbs : Int)*((ibox135 k).hi-(ibox135 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox135
    (computed denominator ibox135) (computed denominator (FixedTape.midBox ibox135))
    (by decide +kernel)
private theorem midpoint_even_135 : ∀ k, 2 ∣ (ibox135 k).lo+(ibox135 k).hi := by decide +kernel
private theorem accepted_135 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox135) tree135 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox135 midpoint_even_135
  simp only [tree135,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox135,candidate_valid h (FixedTape.midBox ibox135),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox135 113 (FixedTape.rowsAux denominator ibox135 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox135) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_135
private noncomputable def tree134 : TapeTree := .split 2 (((105346076635102236158062385365888346641512069745076912689749508021970534400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree135 tree136
attribute [irreducible] tree134
private theorem accepted_134 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox134) tree134 = true := by
  simp only [tree134,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox134 2 (105346076635102236158062385365888346641512069745076912689749508021970534400000000000000000000000 : Int) false,decode_split denominator ibox134 2 (105346076635102236158062385365888346641512069745076912689749508021970534400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_135 h,accepted_136 h⟩
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
private noncomputable def tree131 : TapeTree := .split 2 (((105346076635102236158062385365888346641512069745076912689749508021970534400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree132 tree133
attribute [irreducible] tree131
private theorem accepted_131 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox131) tree131 = true := by
  simp only [tree131,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox131 2 (105346076635102236158062385365888346641512069745076912689749508021970534400000000000000000000000 : Int) false,decode_split denominator ibox131 2 (105346076635102236158062385365888346641512069745076912689749508021970534400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_132 h,accepted_133 h⟩
private noncomputable def tree130 : TapeTree := .split 1 (((46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree131 tree134
attribute [irreducible] tree130
private theorem accepted_130 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox130) tree130 = true := by
  simp only [tree130,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox130 1 (46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) false,decode_split denominator ibox130 1 (46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_131 h,accepted_134 h⟩
private noncomputable def tree129 : TapeTree := .split 2 (((117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree130 tree137
attribute [irreducible] tree129
private theorem accepted_129 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox129) tree129 = true := by
  simp only [tree129,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox129 2 (117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) false,decode_split denominator ibox129 2 (117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_130 h,accepted_137 h⟩
private noncomputable def tree128 : TapeTree := .split 1 (((93640957008979765473833231436345197014677395328957255724221784908418252800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree129 tree144
attribute [irreducible] tree128
private theorem accepted_128 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox128) tree128 = true := by
  simp only [tree128,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox128 1 (93640957008979765473833231436345197014677395328957255724221784908418252800000000000000000000000 : Int) false,decode_split denominator ibox128 1 (93640957008979765473833231436345197014677395328957255724221784908418252800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_129 h,accepted_144 h⟩
private noncomputable def tree127 : TapeTree := .split 2 (((140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree128 tree177
attribute [irreducible] tree127
private theorem accepted_127 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox127) tree127 = true := by
  simp only [tree127,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox127 2 (140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) false,decode_split denominator ibox127 2 (140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_128 h,accepted_177 h⟩
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
private noncomputable def tree124 : TapeTree := .split 1 (((175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree125 tree126
attribute [irreducible] tree124
private theorem accepted_124 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox124) tree124 = true := by
  simp only [tree124,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox124 1 (175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) false,decode_split denominator ibox124 1 (175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) true]
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
private noncomputable def tree121 : TapeTree := .split 1 (((175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree122 tree123
attribute [irreducible] tree121
private theorem accepted_121 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox121) tree121 = true := by
  simp only [tree121,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox121 1 (175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) false,decode_split denominator ibox121 1 (175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_122 h,accepted_123 h⟩
private noncomputable def tree120 : TapeTree := .split 2 (((81935837382857294789604077506802047387842720912837598758694061794865971200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree121 tree124
attribute [irreducible] tree120
private theorem accepted_120 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox120) tree120 = true := by
  simp only [tree120,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox120 2 (81935837382857294789604077506802047387842720912837598758694061794865971200000000000000000000000 : Int) false,decode_split denominator ibox120 2 (81935837382857294789604077506802047387842720912837598758694061794865971200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_121 h,accepted_124 h⟩
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
private noncomputable def tree117 : TapeTree := .split 2 (((81935837382857294789604077506802047387842720912837598758694061794865971200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree118 tree119
attribute [irreducible] tree117
private theorem accepted_117 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox117) tree117 = true := by
  simp only [tree117,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox117 2 (81935837382857294789604077506802047387842720912837598758694061794865971200000000000000000000000 : Int) false,decode_split denominator ibox117 2 (81935837382857294789604077506802047387842720912837598758694061794865971200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_118 h,accepted_119 h⟩
private noncomputable def tree116 : TapeTree := .split 1 (((163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree117 tree120
attribute [irreducible] tree116
private theorem accepted_116 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox116) tree116 = true := by
  simp only [tree116,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox116 1 (163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) false,decode_split denominator ibox116 1 (163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_117 h,accepted_120 h⟩
private noncomputable def tree115 : TapeTree := .centered (candidateRows ibox115) (candidateRows (FixedTape.midBox ibox115))
attribute [irreducible] tree115
private theorem sign_115 : 2*denominator*(computed denominator (FixedTape.midBox ibox115)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox115).gradient k).lo.natAbs ((computed denominator ibox115).gradient k).hi.natAbs : Int)*((ibox115 k).hi-(ibox115 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox115
    (computed denominator ibox115) (computed denominator (FixedTape.midBox ibox115))
    (by decide +kernel)
private theorem midpoint_even_115 : ∀ k, 2 ∣ (ibox115 k).lo+(ibox115 k).hi := by decide +kernel
private theorem accepted_115 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox115) tree115 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox115 midpoint_even_115
  simp only [tree115,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox115,candidate_valid h (FixedTape.midBox ibox115),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox115 113 (FixedTape.rowsAux denominator ibox115 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox115) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_115
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
private noncomputable def tree113 : TapeTree := .split 0 (((151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) : ℚ)/(denominator : ℚ)) tree114 tree115
attribute [irreducible] tree113
private theorem accepted_113 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox113) tree113 = true := by
  simp only [tree113,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox113 0 (151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) false,decode_split denominator ibox113 0 (151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_114 h,accepted_115 h⟩
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
private noncomputable def tree111 : TapeTree := .split 1 (((175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree112 tree113
attribute [irreducible] tree111
private theorem accepted_111 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox111) tree111 = true := by
  simp only [tree111,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox111 1 (175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) false,decode_split denominator ibox111 1 (175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_112 h,accepted_113 h⟩
private noncomputable def tree110 : TapeTree := .centered (candidateRows ibox110) (candidateRows (FixedTape.midBox ibox110))
attribute [irreducible] tree110
private theorem sign_110 : 2*denominator*(computed denominator (FixedTape.midBox ibox110)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox110).gradient k).lo.natAbs ((computed denominator ibox110).gradient k).hi.natAbs : Int)*((ibox110 k).hi-(ibox110 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox110
    (computed denominator ibox110) (computed denominator (FixedTape.midBox ibox110))
    (by decide +kernel)
private theorem midpoint_even_110 : ∀ k, 2 ∣ (ibox110 k).lo+(ibox110 k).hi := by decide +kernel
private theorem accepted_110 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox110) tree110 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox110 midpoint_even_110
  simp only [tree110,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox110,candidate_valid h (FixedTape.midBox ibox110),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox110 113 (FixedTape.rowsAux denominator ibox110 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox110) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_110
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
private noncomputable def tree108 : TapeTree := .split 0 (((151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) : ℚ)/(denominator : ℚ)) tree109 tree110
attribute [irreducible] tree108
private theorem accepted_108 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox108) tree108 = true := by
  simp only [tree108,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox108 0 (151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) false,decode_split denominator ibox108 0 (151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) true]
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
private noncomputable def tree106 : TapeTree := .split 1 (((175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree107 tree108
attribute [irreducible] tree106
private theorem accepted_106 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox106) tree106 = true := by
  simp only [tree106,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox106 1 (175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) false,decode_split denominator ibox106 1 (175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_107 h,accepted_108 h⟩
private noncomputable def tree105 : TapeTree := .split 2 (((58525598130612353421145769647715748134173372080598284827638615567761408000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree106 tree111
attribute [irreducible] tree105
private theorem accepted_105 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox105) tree105 = true := by
  simp only [tree105,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox105 2 (58525598130612353421145769647715748134173372080598284827638615567761408000000000000000000000000 : Int) false,decode_split denominator ibox105 2 (58525598130612353421145769647715748134173372080598284827638615567761408000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_106 h,accepted_111 h⟩
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
private noncomputable def tree103 : TapeTree := .centered (candidateRows ibox103) (candidateRows (FixedTape.midBox ibox103))
attribute [irreducible] tree103
private theorem sign_103 : 2*denominator*(computed denominator (FixedTape.midBox ibox103)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox103).gradient k).lo.natAbs ((computed denominator ibox103).gradient k).hi.natAbs : Int)*((ibox103 k).hi-(ibox103 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox103
    (computed denominator ibox103) (computed denominator (FixedTape.midBox ibox103))
    (by decide +kernel)
private theorem midpoint_even_103 : ∀ k, 2 ∣ (ibox103 k).lo+(ibox103 k).hi := by decide +kernel
private theorem accepted_103 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox103) tree103 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox103 midpoint_even_103
  simp only [tree103,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox103,candidate_valid h (FixedTape.midBox ibox103),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox103 113 (FixedTape.rowsAux denominator ibox103 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox103) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_103
private noncomputable def tree102 : TapeTree := .split 2 (((58525598130612353421145769647715748134173372080598284827638615567761408000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree103 tree104
attribute [irreducible] tree102
private theorem accepted_102 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox102) tree102 = true := by
  simp only [tree102,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox102 2 (58525598130612353421145769647715748134173372080598284827638615567761408000000000000000000000000 : Int) false,decode_split denominator ibox102 2 (58525598130612353421145769647715748134173372080598284827638615567761408000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_103 h,accepted_104 h⟩
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
private noncomputable def tree100 : TapeTree := .split 1 (((152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree101 tree102
attribute [irreducible] tree100
private theorem accepted_100 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox100) tree100 = true := by
  simp only [tree100,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox100 1 (152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 : Int) false,decode_split denominator ibox100 1 (152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_101 h,accepted_102 h⟩
private noncomputable def tree99 : TapeTree := .split 1 (((163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree100 tree105
attribute [irreducible] tree99
private theorem accepted_99 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox99) tree99 = true := by
  simp only [tree99,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox99 1 (163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) false,decode_split denominator ibox99 1 (163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_100 h,accepted_105 h⟩
private noncomputable def tree98 : TapeTree := .split 2 (((70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree99 tree116
attribute [irreducible] tree98
private theorem accepted_98 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox98) tree98 = true := by
  simp only [tree98,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox98 2 (70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 : Int) false,decode_split denominator ibox98 2 (70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_99 h,accepted_116 h⟩
private noncomputable def tree97 : TapeTree := .centered (candidateRows ibox97) (candidateRows (FixedTape.midBox ibox97))
attribute [irreducible] tree97
private theorem sign_97 : 2*denominator*(computed denominator (FixedTape.midBox ibox97)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox97).gradient k).lo.natAbs ((computed denominator ibox97).gradient k).hi.natAbs : Int)*((ibox97 k).hi-(ibox97 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox97
    (computed denominator ibox97) (computed denominator (FixedTape.midBox ibox97))
    (by decide +kernel)
private theorem midpoint_even_97 : ∀ k, 2 ∣ (ibox97 k).lo+(ibox97 k).hi := by decide +kernel
private theorem accepted_97 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox97) tree97 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox97 midpoint_even_97
  simp only [tree97,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox97,candidate_valid h (FixedTape.midBox ibox97),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox97 113 (FixedTape.rowsAux denominator ibox97 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox97) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_97
private noncomputable def tree96 : TapeTree := .centered (candidateRows ibox96) (candidateRows (FixedTape.midBox ibox96))
attribute [irreducible] tree96
private theorem sign_96 : 2*denominator*(computed denominator (FixedTape.midBox ibox96)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox96).gradient k).lo.natAbs ((computed denominator ibox96).gradient k).hi.natAbs : Int)*((ibox96 k).hi-(ibox96 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox96
    (computed denominator ibox96) (computed denominator (FixedTape.midBox ibox96))
    (by decide +kernel)
private theorem midpoint_even_96 : ∀ k, 2 ∣ (ibox96 k).lo+(ibox96 k).hi := by decide +kernel
private theorem accepted_96 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox96) tree96 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox96 midpoint_even_96
  simp only [tree96,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox96,candidate_valid h (FixedTape.midBox ibox96),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox96 113 (FixedTape.rowsAux denominator ibox96 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox96) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_96
private noncomputable def tree95 : TapeTree := .split 2 (((81935837382857294789604077506802047387842720912837598758694061794865971200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree96 tree97
attribute [irreducible] tree95
private theorem accepted_95 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox95) tree95 = true := by
  simp only [tree95,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox95 2 (81935837382857294789604077506802047387842720912837598758694061794865971200000000000000000000000 : Int) false,decode_split denominator ibox95 2 (81935837382857294789604077506802047387842720912837598758694061794865971200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_96 h,accepted_97 h⟩
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
private noncomputable def tree93 : TapeTree := .split 1 (((117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree94 tree95
attribute [irreducible] tree93
private theorem accepted_93 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox93) tree93 = true := by
  simp only [tree93,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox93 1 (117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) false,decode_split denominator ibox93 1 (117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) true]
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
private noncomputable def tree91 : TapeTree := .centered (candidateRows ibox91) (candidateRows (FixedTape.midBox ibox91))
attribute [irreducible] tree91
private theorem sign_91 : 2*denominator*(computed denominator (FixedTape.midBox ibox91)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox91).gradient k).lo.natAbs ((computed denominator ibox91).gradient k).hi.natAbs : Int)*((ibox91 k).hi-(ibox91 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox91
    (computed denominator ibox91) (computed denominator (FixedTape.midBox ibox91))
    (by decide +kernel)
private theorem midpoint_even_91 : ∀ k, 2 ∣ (ibox91 k).lo+(ibox91 k).hi := by decide +kernel
private theorem accepted_91 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox91) tree91 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox91 midpoint_even_91
  simp only [tree91,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox91,candidate_valid h (FixedTape.midBox ibox91),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox91 113 (FixedTape.rowsAux denominator ibox91 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox91) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_91
private noncomputable def tree90 : TapeTree := .split 1 (((117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree91 tree92
attribute [irreducible] tree90
private theorem accepted_90 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox90) tree90 = true := by
  simp only [tree90,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox90 1 (117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) false,decode_split denominator ibox90 1 (117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_91 h,accepted_92 h⟩
private noncomputable def tree89 : TapeTree := .split 2 (((70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree90 tree93
attribute [irreducible] tree89
private theorem accepted_89 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox89) tree89 = true := by
  simp only [tree89,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox89 2 (70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 : Int) false,decode_split denominator ibox89 2 (70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_90 h,accepted_93 h⟩
private noncomputable def tree88 : TapeTree := .split 1 (((140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree89 tree98
attribute [irreducible] tree88
private theorem accepted_88 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox88) tree88 = true := by
  simp only [tree88,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox88 1 (140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) false,decode_split denominator ibox88 1 (140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_89 h,accepted_98 h⟩
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
private noncomputable def tree85 : TapeTree := .split 0 (((151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) : ℚ)/(denominator : ℚ)) tree86 tree87
attribute [irreducible] tree85
private theorem accepted_85 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox85) tree85 = true := by
  simp only [tree85,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox85 0 (151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) false,decode_split denominator ibox85 0 (151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_86 h,accepted_87 h⟩
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
private noncomputable def tree83 : TapeTree := .centered (candidateRows ibox83) (candidateRows (FixedTape.midBox ibox83))
attribute [irreducible] tree83
private theorem sign_83 : 2*denominator*(computed denominator (FixedTape.midBox ibox83)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox83).gradient k).lo.natAbs ((computed denominator ibox83).gradient k).hi.natAbs : Int)*((ibox83 k).hi-(ibox83 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox83
    (computed denominator ibox83) (computed denominator (FixedTape.midBox ibox83))
    (by decide +kernel)
private theorem midpoint_even_83 : ∀ k, 2 ∣ (ibox83 k).lo+(ibox83 k).hi := by decide +kernel
private theorem accepted_83 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox83) tree83 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox83 midpoint_even_83
  simp only [tree83,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox83,candidate_valid h (FixedTape.midBox ibox83),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox83 113 (FixedTape.rowsAux denominator ibox83 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox83) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_83
private noncomputable def tree82 : TapeTree := .split 0 (((151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) : ℚ)/(denominator : ℚ)) tree83 tree84
attribute [irreducible] tree82
private theorem accepted_82 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox82) tree82 = true := by
  simp only [tree82,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox82 0 (151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) false,decode_split denominator ibox82 0 (151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_83 h,accepted_84 h⟩
private noncomputable def tree81 : TapeTree := .split 1 (((181429354204898295605551885907918819215937453449854682965679708260060364800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree82 tree85
attribute [irreducible] tree81
private theorem accepted_81 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox81) tree81 = true := by
  simp only [tree81,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox81 1 (181429354204898295605551885907918819215937453449854682965679708260060364800000000000000000000000 : Int) false,decode_split denominator ibox81 1 (181429354204898295605551885907918819215937453449854682965679708260060364800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_82 h,accepted_85 h⟩
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
private noncomputable def tree78 : TapeTree := .split 2 (((29262799065306176710572884823857874067086686040299142413819307783880704000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree79 tree80
attribute [irreducible] tree78
private theorem accepted_78 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox78) tree78 = true := by
  simp only [tree78,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox78 2 (29262799065306176710572884823857874067086686040299142413819307783880704000000000000000000000000 : Int) false,decode_split denominator ibox78 2 (29262799065306176710572884823857874067086686040299142413819307783880704000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_79 h,accepted_80 h⟩
private noncomputable def tree77 : TapeTree := .face 1 true (candidateRows ibox77) tree78
attribute [irreducible] tree77
private theorem sign_77 : 0 ≤ ((computed denominator ibox77).gradient 1).lo := by decide +kernel
private theorem accepted_77 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox77) tree77 = true := by
  simp only [tree77,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox77,?_,accepted_78 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox77)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox77).gradient 1).lo) denominator_positive).2 sign_77
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
private noncomputable def tree75 : TapeTree := .face 1 true (candidateRows ibox75) tree76
attribute [irreducible] tree75
private theorem sign_75 : 0 ≤ ((computed denominator ibox75).gradient 1).lo := by decide +kernel
private theorem accepted_75 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox75) tree75 = true := by
  simp only [tree75,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox75,?_,accepted_76 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox75)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox75).gradient 1).lo) denominator_positive).2 sign_75
private noncomputable def tree74 : TapeTree := .split 1 (((181429354204898295605551885907918819215937453449854682965679708260060364800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree75 tree77
attribute [irreducible] tree74
private theorem accepted_74 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox74) tree74 = true := by
  simp only [tree74,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox74 1 (181429354204898295605551885907918819215937453449854682965679708260060364800000000000000000000000 : Int) false,decode_split denominator ibox74 1 (181429354204898295605551885907918819215937453449854682965679708260060364800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_75 h,accepted_77 h⟩
private noncomputable def tree73 : TapeTree := .split 2 (((35115358878367412052687461788629448880504023248358970896583169340656844800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree74 tree81
attribute [irreducible] tree73
private theorem accepted_73 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox73) tree73 = true := by
  simp only [tree73,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox73 2 (35115358878367412052687461788629448880504023248358970896583169340656844800000000000000000000000 : Int) false,decode_split denominator ibox73 2 (35115358878367412052687461788629448880504023248358970896583169340656844800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_74 h,accepted_81 h⟩
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
private noncomputable def tree71 : TapeTree := .centered (candidateRows ibox71) (candidateRows (FixedTape.midBox ibox71))
attribute [irreducible] tree71
private theorem sign_71 : 2*denominator*(computed denominator (FixedTape.midBox ibox71)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox71).gradient k).lo.natAbs ((computed denominator ibox71).gradient k).hi.natAbs : Int)*((ibox71 k).hi-(ibox71 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox71
    (computed denominator ibox71) (computed denominator (FixedTape.midBox ibox71))
    (by decide +kernel)
private theorem midpoint_even_71 : ∀ k, 2 ∣ (ibox71 k).lo+(ibox71 k).hi := by decide +kernel
private theorem accepted_71 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox71) tree71 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox71 midpoint_even_71
  simp only [tree71,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox71,candidate_valid h (FixedTape.midBox ibox71),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox71 113 (FixedTape.rowsAux denominator ibox71 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox71) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_71
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
private noncomputable def tree69 : TapeTree := .split 1 (((169724234578775824921322731978375669589102779033735026000151985146508083200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree70 tree71
attribute [irreducible] tree69
private theorem accepted_69 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox69) tree69 = true := by
  simp only [tree69,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox69 1 (169724234578775824921322731978375669589102779033735026000151985146508083200000000000000000000000 : Int) false,decode_split denominator ibox69 1 (169724234578775824921322731978375669589102779033735026000151985146508083200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_70 h,accepted_71 h⟩
private noncomputable def tree68 : TapeTree := .split 2 (((35115358878367412052687461788629448880504023248358970896583169340656844800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree69 tree72
attribute [irreducible] tree68
private theorem accepted_68 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox68) tree68 = true := by
  simp only [tree68,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox68 2 (35115358878367412052687461788629448880504023248358970896583169340656844800000000000000000000000 : Int) false,decode_split denominator ibox68 2 (35115358878367412052687461788629448880504023248358970896583169340656844800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_69 h,accepted_72 h⟩
private noncomputable def tree67 : TapeTree := .split 1 (((175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree68 tree73
attribute [irreducible] tree67
private theorem accepted_67 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox67) tree67 = true := by
  simp only [tree67,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox67 1 (175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) false,decode_split denominator ibox67 1 (175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_68 h,accepted_73 h⟩
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
private noncomputable def tree65 : TapeTree := .centered (candidateRows ibox65) (candidateRows (FixedTape.midBox ibox65))
attribute [irreducible] tree65
private theorem sign_65 : 2*denominator*(computed denominator (FixedTape.midBox ibox65)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox65).gradient k).lo.natAbs ((computed denominator ibox65).gradient k).hi.natAbs : Int)*((ibox65 k).hi-(ibox65 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox65
    (computed denominator ibox65) (computed denominator (FixedTape.midBox ibox65))
    (by decide +kernel)
private theorem midpoint_even_65 : ∀ k, 2 ∣ (ibox65 k).lo+(ibox65 k).hi := by decide +kernel
private theorem accepted_65 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox65) tree65 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox65 midpoint_even_65
  simp only [tree65,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox65,candidate_valid h (FixedTape.midBox ibox65),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox65 113 (FixedTape.rowsAux denominator ibox65 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox65) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_65
private noncomputable def tree64 : TapeTree := .split 0 (((151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) : ℚ)/(denominator : ℚ)) tree65 tree66
attribute [irreducible] tree64
private theorem accepted_64 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox64) tree64 = true := by
  simp only [tree64,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox64 0 (151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) false,decode_split denominator ibox64 0 (151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_65 h,accepted_66 h⟩
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
private noncomputable def tree61 : TapeTree := .split 0 (((151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) : ℚ)/(denominator : ℚ)) tree62 tree63
attribute [irreducible] tree61
private theorem accepted_61 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox61) tree61 = true := by
  simp only [tree61,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox61 0 (151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) false,decode_split denominator ibox61 0 (151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_62 h,accepted_63 h⟩
private noncomputable def tree60 : TapeTree := .split 2 (((17557679439183706026343730894314724440252011624179485448291584670328422400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree61 tree64
attribute [irreducible] tree60
private theorem accepted_60 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox60) tree60 = true := by
  simp only [tree60,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox60 2 (17557679439183706026343730894314724440252011624179485448291584670328422400000000000000000000000 : Int) false,decode_split denominator ibox60 2 (17557679439183706026343730894314724440252011624179485448291584670328422400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_61 h,accepted_64 h⟩
private noncomputable def tree59 : TapeTree := .centered (candidateRows ibox59) (candidateRows (FixedTape.midBox ibox59))
attribute [irreducible] tree59
private theorem sign_59 : 2*denominator*(computed denominator (FixedTape.midBox ibox59)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox59).gradient k).lo.natAbs ((computed denominator ibox59).gradient k).hi.natAbs : Int)*((ibox59 k).hi-(ibox59 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox59
    (computed denominator ibox59) (computed denominator (FixedTape.midBox ibox59))
    (by decide +kernel)
private theorem midpoint_even_59 : ∀ k, 2 ∣ (ibox59 k).lo+(ibox59 k).hi := by decide +kernel
private theorem accepted_59 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox59) tree59 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox59 midpoint_even_59
  simp only [tree59,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox59,candidate_valid h (FixedTape.midBox ibox59),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox59 113 (FixedTape.rowsAux denominator ibox59 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox59) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_59
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
private noncomputable def tree56 : TapeTree := .split 2 (((8778839719591853013171865447157362220126005812089742724145792335164211200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree57 tree58
attribute [irreducible] tree56
private theorem accepted_56 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox56) tree56 = true := by
  simp only [tree56,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox56 2 (8778839719591853013171865447157362220126005812089742724145792335164211200000000000000000000000 : Int) false,decode_split denominator ibox56 2 (8778839719591853013171865447157362220126005812089742724145792335164211200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_57 h,accepted_58 h⟩
private noncomputable def tree55 : TapeTree := .split 0 (((151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) : ℚ)/(denominator : ℚ)) tree56 tree59
attribute [irreducible] tree55
private theorem accepted_55 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox55) tree55 = true := by
  simp only [tree55,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox55 0 (151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) false,decode_split denominator ibox55 0 (151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_56 h,accepted_59 h⟩
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
private noncomputable def tree52 : TapeTree := .centered (candidateRows ibox52) (candidateRows (FixedTape.midBox ibox52))
attribute [irreducible] tree52
private theorem sign_52 : 2*denominator*(computed denominator (FixedTape.midBox ibox52)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox52).gradient k).lo.natAbs ((computed denominator ibox52).gradient k).hi.natAbs : Int)*((ibox52 k).hi-(ibox52 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox52
    (computed denominator ibox52) (computed denominator (FixedTape.midBox ibox52))
    (by decide +kernel)
private theorem midpoint_even_52 : ∀ k, 2 ∣ (ibox52 k).lo+(ibox52 k).hi := by decide +kernel
private theorem accepted_52 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox52) tree52 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox52 midpoint_even_52
  simp only [tree52,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox52,candidate_valid h (FixedTape.midBox ibox52),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox52 113 (FixedTape.rowsAux denominator ibox52 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox52) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_52
private noncomputable def tree51 : TapeTree := .split 0 (((151678841821837019071168019969655496375507037187057122000876589645023506540726163613941760000000 : Int) : ℚ)/(denominator : ℚ)) tree52 tree53
attribute [irreducible] tree51
private theorem accepted_51 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox51) tree51 = true := by
  simp only [tree51,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox51 0 (151678841821837019071168019969655496375507037187057122000876589645023506540726163613941760000000 : Int) false,decode_split denominator ibox51 0 (151678841821837019071168019969655496375507037187057122000876589645023506540726163613941760000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_52 h,accepted_53 h⟩
private noncomputable def tree50 : TapeTree := .split 2 (((2926279906530617671057288482385787406708668604029914241381930778388070400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree51 tree54
attribute [irreducible] tree50
private theorem accepted_50 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox50) tree50 = true := by
  simp only [tree50,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox50 2 (2926279906530617671057288482385787406708668604029914241381930778388070400000000000000000000000 : Int) false,decode_split denominator ibox50 2 (2926279906530617671057288482385787406708668604029914241381930778388070400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_51 h,accepted_54 h⟩
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
private noncomputable def tree47 : TapeTree := .centered (candidateRows ibox47) (candidateRows (FixedTape.midBox ibox47))
attribute [irreducible] tree47
private theorem sign_47 : 2*denominator*(computed denominator (FixedTape.midBox ibox47)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox47).gradient k).lo.natAbs ((computed denominator ibox47).gradient k).hi.natAbs : Int)*((ibox47 k).hi-(ibox47 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox47
    (computed denominator ibox47) (computed denominator (FixedTape.midBox ibox47))
    (by decide +kernel)
private theorem midpoint_even_47 : ∀ k, 2 ∣ (ibox47 k).lo+(ibox47 k).hi := by decide +kernel
private theorem accepted_47 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox47) tree47 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox47 midpoint_even_47
  simp only [tree47,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox47,candidate_valid h (FixedTape.midBox ibox47),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox47 113 (FixedTape.rowsAux denominator ibox47 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox47) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_47
private noncomputable def tree46 : TapeTree := .split 0 (((150703415186326819423546057740844598828819576742060284898908967982711198022178490841825280000000 : Int) : ℚ)/(denominator : ℚ)) tree47 tree48
attribute [irreducible] tree46
private theorem accepted_46 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox46) tree46 = true := by
  simp only [tree46,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox46 0 (150703415186326819423546057740844598828819576742060284898908967982711198022178490841825280000000 : Int) false,decode_split denominator ibox46 0 (150703415186326819423546057740844598828819576742060284898908967982711198022178490841825280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_47 h,accepted_48 h⟩
private noncomputable def tree45 : TapeTree := .split 2 (((2926279906530617671057288482385787406708668604029914241381930778388070400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree46 tree49
attribute [irreducible] tree45
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox45 2 (2926279906530617671057288482385787406708668604029914241381930778388070400000000000000000000000 : Int) false,decode_split denominator ibox45 2 (2926279906530617671057288482385787406708668604029914241381930778388070400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_46 h,accepted_49 h⟩
private noncomputable def tree44 : TapeTree := .split 0 (((151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) : ℚ)/(denominator : ℚ)) tree45 tree50
attribute [irreducible] tree44
private theorem accepted_44 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox44) tree44 = true := by
  simp only [tree44,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox44 0 (151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) false,decode_split denominator ibox44 0 (151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_45 h,accepted_50 h⟩
private noncomputable def tree43 : TapeTree := .split 2 (((5852559813061235342114576964771574813417337208059828482763861556776140800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree44 tree55
attribute [irreducible] tree43
private theorem accepted_43 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox43) tree43 = true := by
  simp only [tree43,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox43 2 (5852559813061235342114576964771574813417337208059828482763861556776140800000000000000000000000 : Int) false,decode_split denominator ibox43 2 (5852559813061235342114576964771574813417337208059828482763861556776140800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_44 h,accepted_55 h⟩
private noncomputable def tree42 : TapeTree := .split 2 (((11705119626122470684229153929543149626834674416119656965527723113552281600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree43 tree60
attribute [irreducible] tree42
private theorem accepted_42 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox42) tree42 = true := by
  simp only [tree42,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox42 2 (11705119626122470684229153929543149626834674416119656965527723113552281600000000000000000000000 : Int) false,decode_split denominator ibox42 2 (11705119626122470684229153929543149626834674416119656965527723113552281600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_43 h,accepted_60 h⟩
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
private noncomputable def tree40 : TapeTree := .centered (candidateRows ibox40) (candidateRows (FixedTape.midBox ibox40))
attribute [irreducible] tree40
private theorem sign_40 : 2*denominator*(computed denominator (FixedTape.midBox ibox40)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox40).gradient k).lo.natAbs ((computed denominator ibox40).gradient k).hi.natAbs : Int)*((ibox40 k).hi-(ibox40 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox40
    (computed denominator ibox40) (computed denominator (FixedTape.midBox ibox40))
    (by decide +kernel)
private theorem midpoint_even_40 : ∀ k, 2 ∣ (ibox40 k).lo+(ibox40 k).hi := by decide +kernel
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox40 midpoint_even_40
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox40,candidate_valid h (FixedTape.midBox ibox40),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox40 113 (FixedTape.rowsAux denominator ibox40 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox40) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_40
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
private noncomputable def tree38 : TapeTree := .split 2 (((11705119626122470684229153929543149626834674416119656965527723113552281600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree39 tree40
attribute [irreducible] tree38
private theorem accepted_38 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox38) tree38 = true := by
  simp only [tree38,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox38 2 (11705119626122470684229153929543149626834674416119656965527723113552281600000000000000000000000 : Int) false,decode_split denominator ibox38 2 (11705119626122470684229153929543149626834674416119656965527723113552281600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_39 h,accepted_40 h⟩
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
private noncomputable def tree36 : TapeTree := .split 1 (((175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree37 tree41
attribute [irreducible] tree36
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox36 1 (175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) false,decode_split denominator ibox36 1 (175576794391837060263437308943147244402520116241794854482915846703284224000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_37 h,accepted_41 h⟩
private noncomputable def tree35 : TapeTree := .split 2 (((23410239252244941368458307859086299253669348832239313931055446227104563200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree36 tree67
attribute [irreducible] tree35
private theorem accepted_35 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox35) tree35 = true := by
  simp only [tree35,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox35 2 (23410239252244941368458307859086299253669348832239313931055446227104563200000000000000000000000 : Int) false,decode_split denominator ibox35 2 (23410239252244941368458307859086299253669348832239313931055446227104563200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_36 h,accepted_67 h⟩
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
private noncomputable def tree33 : TapeTree := .centered (candidateRows ibox33) (candidateRows (FixedTape.midBox ibox33))
attribute [irreducible] tree33
private theorem sign_33 : 2*denominator*(computed denominator (FixedTape.midBox ibox33)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox33).gradient k).lo.natAbs ((computed denominator ibox33).gradient k).hi.natAbs : Int)*((ibox33 k).hi-(ibox33 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox33
    (computed denominator ibox33) (computed denominator (FixedTape.midBox ibox33))
    (by decide +kernel)
private theorem midpoint_even_33 : ∀ k, 2 ∣ (ibox33 k).lo+(ibox33 k).hi := by decide +kernel
private theorem accepted_33 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox33) tree33 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox33 midpoint_even_33
  simp only [tree33,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox33,candidate_valid h (FixedTape.midBox ibox33),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox33 113 (FixedTape.rowsAux denominator ibox33 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox33) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_33
private noncomputable def tree32 : TapeTree := .split 0 (((151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) : ℚ)/(denominator : ℚ)) tree33 tree34
attribute [irreducible] tree32
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox32 0 (151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) false,decode_split denominator ibox32 0 (151191128504081919247357038855250047602163306964558703449892778813867352281452327227883520000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_33 h,accepted_34 h⟩
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
private noncomputable def tree30 : TapeTree := .split 1 (((152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree31 tree32
attribute [irreducible] tree30
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox30 1 (152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 : Int) false,decode_split denominator ibox30 1 (152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 : Int) true]
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
private noncomputable def tree28 : TapeTree := .centered (candidateRows ibox28) (candidateRows (FixedTape.midBox ibox28))
attribute [irreducible] tree28
private theorem sign_28 : 2*denominator*(computed denominator (FixedTape.midBox ibox28)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox28).gradient k).lo.natAbs ((computed denominator ibox28).gradient k).hi.natAbs : Int)*((ibox28 k).hi-(ibox28 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox28
    (computed denominator ibox28) (computed denominator (FixedTape.midBox ibox28))
    (by decide +kernel)
private theorem midpoint_even_28 : ∀ k, 2 ∣ (ibox28 k).lo+(ibox28 k).hi := by decide +kernel
private theorem accepted_28 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox28) tree28 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox28 midpoint_even_28
  simp only [tree28,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox28,candidate_valid h (FixedTape.midBox ibox28),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox28 113 (FixedTape.rowsAux denominator ibox28 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox28) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_28
private noncomputable def tree27 : TapeTree := .split 1 (((152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree28 tree29
attribute [irreducible] tree27
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox27 1 (152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 : Int) false,decode_split denominator ibox27 1 (152166555139592118894979001084060945148850767409555540551860400476179660800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_28 h,accepted_29 h⟩
private noncomputable def tree26 : TapeTree := .split 2 (((23410239252244941368458307859086299253669348832239313931055446227104563200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree27 tree30
attribute [irreducible] tree26
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox26 2 (23410239252244941368458307859086299253669348832239313931055446227104563200000000000000000000000 : Int) false,decode_split denominator ibox26 2 (23410239252244941368458307859086299253669348832239313931055446227104563200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_27 h,accepted_30 h⟩
private noncomputable def tree25 : TapeTree := .split 1 (((163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree26 tree35
attribute [irreducible] tree25
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox25 1 (163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) false,decode_split denominator ibox25 1 (163871674765714589579208155013604094775685441825675197517388123589731942400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_26 h,accepted_35 h⟩
private noncomputable def tree24 : TapeTree := .centered (candidateRows ibox24) (candidateRows (FixedTape.midBox ibox24))
attribute [irreducible] tree24
private theorem sign_24 : 2*denominator*(computed denominator (FixedTape.midBox ibox24)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox24).gradient k).lo.natAbs ((computed denominator ibox24).gradient k).hi.natAbs : Int)*((ibox24 k).hi-(ibox24 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox24
    (computed denominator ibox24) (computed denominator (FixedTape.midBox ibox24))
    (by decide +kernel)
private theorem midpoint_even_24 : ∀ k, 2 ∣ (ibox24 k).lo+(ibox24 k).hi := by decide +kernel
private theorem accepted_24 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox24) tree24 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox24 midpoint_even_24
  simp only [tree24,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox24,candidate_valid h (FixedTape.midBox ibox24),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox24 113 (FixedTape.rowsAux denominator ibox24 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox24) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_24
private noncomputable def tree23 : TapeTree := .centered (candidateRows ibox23) (candidateRows (FixedTape.midBox ibox23))
attribute [irreducible] tree23
private theorem sign_23 : 2*denominator*(computed denominator (FixedTape.midBox ibox23)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox23).gradient k).lo.natAbs ((computed denominator ibox23).gradient k).hi.natAbs : Int)*((ibox23 k).hi-(ibox23 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox23
    (computed denominator ibox23) (computed denominator (FixedTape.midBox ibox23))
    (by decide +kernel)
private theorem midpoint_even_23 : ∀ k, 2 ∣ (ibox23 k).lo+(ibox23 k).hi := by decide +kernel
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox23 midpoint_even_23
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox23,candidate_valid h (FixedTape.midBox ibox23),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox23 113 (FixedTape.rowsAux denominator ibox23 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox23) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_23
private noncomputable def tree22 : TapeTree := .split 2 (((23410239252244941368458307859086299253669348832239313931055446227104563200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree23 tree24
attribute [irreducible] tree22
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox22 2 (23410239252244941368458307859086299253669348832239313931055446227104563200000000000000000000000 : Int) false,decode_split denominator ibox22 2 (23410239252244941368458307859086299253669348832239313931055446227104563200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_23 h,accepted_24 h⟩
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
private noncomputable def tree20 : TapeTree := .split 1 (((117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree21 tree22
attribute [irreducible] tree20
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox20 1 (117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) false,decode_split denominator ibox20 1 (117051196261224706842291539295431496268346744161196569655277231135522816000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_21 h,accepted_22 h⟩
private noncomputable def tree19 : TapeTree := .split 1 (((140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree25
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 1 (140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) false,decode_split denominator ibox19 1 (140461435513469648210749847154517795522016092993435883586332677362627379200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_20 h,accepted_25 h⟩
private noncomputable def tree18 : TapeTree := .split 2 (((46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree19 tree88
attribute [irreducible] tree18
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox18 2 (46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) false,decode_split denominator ibox18 2 (46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_19 h,accepted_88 h⟩
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
private noncomputable def tree16 : TapeTree := .centered (candidateRows ibox16) (candidateRows (FixedTape.midBox ibox16))
attribute [irreducible] tree16
private theorem sign_16 : 2*denominator*(computed denominator (FixedTape.midBox ibox16)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox16).gradient k).lo.natAbs ((computed denominator ibox16).gradient k).hi.natAbs : Int)*((ibox16 k).hi-(ibox16 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox16
    (computed denominator ibox16) (computed denominator (FixedTape.midBox ibox16))
    (by decide +kernel)
private theorem midpoint_even_16 : ∀ k, 2 ∣ (ibox16 k).lo+(ibox16 k).hi := by decide +kernel
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox16 midpoint_even_16
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox16,candidate_valid h (FixedTape.midBox ibox16),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox16 113 (FixedTape.rowsAux denominator ibox16 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox16) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_16
private noncomputable def tree15 : TapeTree := .split 1 (((70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree16 tree17
attribute [irreducible] tree15
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox15 1 (70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 : Int) false,decode_split denominator ibox15 1 (70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_16 h,accepted_17 h⟩
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
private noncomputable def tree13 : TapeTree := .split 2 (((70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree14 tree15
attribute [irreducible] tree13
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox13 2 (70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 : Int) false,decode_split denominator ibox13 2 (70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_14 h,accepted_15 h⟩
private noncomputable def tree12 : TapeTree := .centered (candidateRows ibox12) (candidateRows (FixedTape.midBox ibox12))
attribute [irreducible] tree12
private theorem sign_12 : 2*denominator*(computed denominator (FixedTape.midBox ibox12)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox12).gradient k).lo.natAbs ((computed denominator ibox12).gradient k).hi.natAbs : Int)*((ibox12 k).hi-(ibox12 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox12
    (computed denominator ibox12) (computed denominator (FixedTape.midBox ibox12))
    (by decide +kernel)
private theorem midpoint_even_12 : ∀ k, 2 ∣ (ibox12 k).lo+(ibox12 k).hi := by decide +kernel
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox12 midpoint_even_12
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox12,candidate_valid h (FixedTape.midBox ibox12),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox12 113 (FixedTape.rowsAux denominator ibox12 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox12) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_12
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
private noncomputable def tree10 : TapeTree := .split 2 (((70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree11 tree12
attribute [irreducible] tree10
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox10 2 (70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 : Int) false,decode_split denominator ibox10 2 (70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_11 h,accepted_12 h⟩
private noncomputable def tree9 : TapeTree := .split 1 (((46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree10 tree13
attribute [irreducible] tree9
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox9 1 (46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) false,decode_split denominator ibox9 1 (46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_10 h,accepted_13 h⟩
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
private noncomputable def tree6 : TapeTree := .split 1 (((70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree8
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 1 (70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 : Int) false,decode_split denominator ibox6 1 (70230717756734824105374923577258897761008046496717941793166338681313689600000000000000000000000 : Int) true]
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
private noncomputable def tree4 : TapeTree := .split 1 (((46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree6
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 1 (46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) false,decode_split denominator ibox4 1 (46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_6 h⟩
private noncomputable def tree3 : TapeTree := .split 2 (((46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree9
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 2 (46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) false,decode_split denominator ibox3 2 (46820478504489882736916615718172598507338697664478627862110892454209126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_9 h⟩
private noncomputable def tree2 : TapeTree := .split 1 (((93640957008979765473833231436345197014677395328957255724221784908418252800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree18
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 1 (93640957008979765473833231436345197014677395328957255724221784908418252800000000000000000000000 : Int) false,decode_split denominator ibox2 1 (93640957008979765473833231436345197014677395328957255724221784908418252800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_18 h⟩
private noncomputable def tree1 : TapeTree := .split 2 (((93640957008979765473833231436345197014677395328957255724221784908418252800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree2 tree127
attribute [irreducible] tree1
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox1 2 (93640957008979765473833231436345197014677395328957255724221784908418252800000000000000000000000 : Int) false,decode_split denominator ibox1 2 (93640957008979765473833231436345197014677395328957255724221784908418252800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_2 h,accepted_127 h⟩
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
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (4010416666666667/5000000000000000 : ℚ) (13/16 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 113 = e123 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (4010416666666667/5000000000000000 : ℚ) (13/16 : ℚ)) x → eval e123 x ≤ 0 := by
  have hb := h.child_4 tape 113 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell107_high_internal_top

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell107_high_internal_top
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((4010416666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((13/16 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 107 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 107 p)
    (hkb : ((13/16 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((4010416666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : bStar < a), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell107_high_internal_top.cell_bound h.child_8 h.child_9 (Cell107_high_internal_top.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell107_high_internal_top
