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
namespace Cell109_high_internal_top
private noncomputable def qValues : Fin 2 → ℚ := ![(10762599712598610900494953266459034562/4969967832003321605972598600035610253 : ℚ),(-7132045245167417526875000000000000000/14909903496009964817917795800106830759 : ℚ)]
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
    priceLambda 109 p = ((10762599712598610900494953266459034562/4969967832003321605972598600035610253 : ℝ)+(-7132045245167417526875000000000000000/14909903496009964817917795800106830759 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell109,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 109 p = 0 := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell109,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e123 x = (x 0*(1-x 0))*(aPoint x+priceLambda 109 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 109 (x 0)*psiStar (rPoint x)+(cStar-aPoint x-eta (0 : Fin 9)*psiStar (aPoint x))-(cStar-capPoint x-eta (0 : Fin 9)*psiStar (capPoint x))) := by
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
    (hL : lambdaStar (x 0) = priceLambda 109 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 109 (x 0)) :
    (1)*eval e123 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_neg (not_le.mpr ha),if_neg (not_le.mpr hA),hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (4114583333333333/5000000000000000 : ℚ) (4166666666666667/5000000000000000 : ℚ)) x → eval e123 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((4114583333333333/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((4166666666666667/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 109 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 109 p)
    (hkb : ((4166666666666667/5000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((4114583333333333/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : bStar < a) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h7 (4114583333333333/5000000000000000 : ℚ) (4166666666666667/5000000000000000 : ℚ) bStar p a A r hpcell hkb hr.2 hap hcase hpA hAr
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 109 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 109 (x 0) := by simpa only [hxp] using hT
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
.const (10762599712598610900494953266459034562/4969967832003321605972598600035610253 : ℚ),
.const (-7132045245167417526875000000000000000/14909903496009964817917795800106830759 : ℚ),
.mul 104 1,
.add 103 105,
.mul 1 10,
.add 8 38,
.neg 55,
.add 108 109,
.mul 110 107,
.mul 106 102,
.add 111 112]
private noncomputable def ssaQVals : Fin 15 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(-2840189/5000000 : ℚ),(113609/200000 : ℚ),(1085/4818 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ),(4818/3733 : ℚ),(145513/100000 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(10762599712598610900494953266459034562/4969967832003321605972598600035610253 : ℚ),(-7132045245167417526875000000000000000/14909903496009964817917795800106830759 : ℚ)]
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
private noncomputable def denominator : Int := 177050825412997995922413541706401171451169671596626045709440141658737868800000000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨145698075079446255674431116162692902512455595157978753370415343464933323903990556084142080000000,147542354510831675072066312288534037703544173423933134835844891157351271296009443915857920000000⟩,⟨0,177050825412997995922413541706401171451169671596626045709440141658737868800000000000000000000000⟩,⟨0,177050825412997995922413541706401171451169671596626045709440141658737868800000000000000000000000⟩,⟨0,177050825412997995922413541706401171451169671596626045709440141658737868800000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 3 true
private noncomputable def ibox2 : Fin 4 → FixedTape.I := splitI ibox1 2 88525412706498997961206770853200585725584835798313022854720070829368934400000000000000000000000 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 1 88525412706498997961206770853200585725584835798313022854720070829368934400000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 2 44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 1 44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox4 1 44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 true
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 1 66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox6 1 66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox3 2 44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox9 1 44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 false
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox10 2 66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 false
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox10 2 66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 true
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox9 1 44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 true
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox13 2 66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 false
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox13 2 66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 true
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox15 1 66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 false
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox15 1 66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 true
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox2 1 88525412706498997961206770853200585725584835798313022854720070829368934400000000000000000000000 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox18 2 44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 false
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 1 132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox20 1 110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 false
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox20 1 110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 true
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox22 2 22131353176624749490301692713300146431396208949578255713680017707342233600000000000000000000000 false
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox22 2 22131353176624749490301692713300146431396208949578255713680017707342233600000000000000000000000 true
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox19 1 132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 true
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox25 1 154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 false
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox26 2 22131353176624749490301692713300146431396208949578255713680017707342233600000000000000000000000 false
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox27 1 143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 false
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox27 1 143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 true
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox26 2 22131353176624749490301692713300146431396208949578255713680017707342233600000000000000000000000 true
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox30 1 143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 false
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox30 1 143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 true
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox25 1 154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 true
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox33 2 22131353176624749490301692713300146431396208949578255713680017707342233600000000000000000000000 false
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox34 1 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 false
private noncomputable def ibox36 : Fin 4 → FixedTape.I := faceI ibox35 1 true
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox36 2 11065676588312374745150846356650073215698104474789127856840008853671116800000000000000000000000 false
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox36 2 11065676588312374745150846356650073215698104474789127856840008853671116800000000000000000000000 true
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox34 1 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 true
private noncomputable def ibox40 : Fin 4 → FixedTape.I := faceI ibox39 1 true
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox40 2 11065676588312374745150846356650073215698104474789127856840008853671116800000000000000000000000 false
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox41 0 146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 false
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox42 2 5532838294156187372575423178325036607849052237394563928420004426835558400000000000000000000000 false
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox43 2 2766419147078093686287711589162518303924526118697281964210002213417779200000000000000000000000 false
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox43 2 2766419147078093686287711589162518303924526118697281964210002213417779200000000000000000000000 true
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox42 2 5532838294156187372575423178325036607849052237394563928420004426835558400000000000000000000000 true
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox41 0 146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 true
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox47 2 5532838294156187372575423178325036607849052237394563928420004426835558400000000000000000000000 false
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox48 2 2766419147078093686287711589162518303924526118697281964210002213417779200000000000000000000000 false
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox48 2 2766419147078093686287711589162518303924526118697281964210002213417779200000000000000000000000 true
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox47 2 5532838294156187372575423178325036607849052237394563928420004426835558400000000000000000000000 true
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox40 2 11065676588312374745150846356650073215698104474789127856840008853671116800000000000000000000000 true
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox52 0 146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 false
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox53 2 16598514882468562117726269534975109823547156712183691785260013280506675200000000000000000000000 false
private noncomputable def ibox55 : Fin 4 → FixedTape.I := splitI ibox53 2 16598514882468562117726269534975109823547156712183691785260013280506675200000000000000000000000 true
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox52 0 146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 true
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox33 2 22131353176624749490301692713300146431396208949578255713680017707342233600000000000000000000000 true
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox57 1 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 false
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox58 2 33197029764937124235452539069950219647094313424367383570520026561013350400000000000000000000000 false
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox59 1 160452310530529433804687272171426061627622514884442353924180128378231193600000000000000000000000 false
private noncomputable def ibox61 : Fin 4 → FixedTape.I := splitI ibox59 1 160452310530529433804687272171426061627622514884442353924180128378231193600000000000000000000000 true
private noncomputable def ibox62 : Fin 4 → FixedTape.I := splitI ibox58 2 33197029764937124235452539069950219647094313424367383570520026561013350400000000000000000000000 true
private noncomputable def ibox63 : Fin 4 → FixedTape.I := splitI ibox57 1 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 true
private noncomputable def ibox64 : Fin 4 → FixedTape.I := splitI ibox63 2 33197029764937124235452539069950219647094313424367383570520026561013350400000000000000000000000 false
private noncomputable def ibox65 : Fin 4 → FixedTape.I := splitI ibox64 1 171517987118841808549838118528076134843320619359231481781020137231902310400000000000000000000000 false
private noncomputable def ibox66 : Fin 4 → FixedTape.I := faceI ibox65 1 true
private noncomputable def ibox67 : Fin 4 → FixedTape.I := splitI ibox64 1 171517987118841808549838118528076134843320619359231481781020137231902310400000000000000000000000 true
private noncomputable def ibox68 : Fin 4 → FixedTape.I := splitI ibox67 0 146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 false
private noncomputable def ibox69 : Fin 4 → FixedTape.I := faceI ibox68 1 true
private noncomputable def ibox70 : Fin 4 → FixedTape.I := splitI ibox67 0 146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 true
private noncomputable def ibox71 : Fin 4 → FixedTape.I := splitI ibox63 2 33197029764937124235452539069950219647094313424367383570520026561013350400000000000000000000000 true
private noncomputable def ibox72 : Fin 4 → FixedTape.I := splitI ibox71 1 171517987118841808549838118528076134843320619359231481781020137231902310400000000000000000000000 false
private noncomputable def ibox73 : Fin 4 → FixedTape.I := splitI ibox71 1 171517987118841808549838118528076134843320619359231481781020137231902310400000000000000000000000 true
private noncomputable def ibox74 : Fin 4 → FixedTape.I := splitI ibox73 0 146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 false
private noncomputable def ibox75 : Fin 4 → FixedTape.I := splitI ibox73 0 146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 true
private noncomputable def ibox76 : Fin 4 → FixedTape.I := splitI ibox18 2 44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 true
private noncomputable def ibox77 : Fin 4 → FixedTape.I := splitI ibox76 1 132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 false
private noncomputable def ibox78 : Fin 4 → FixedTape.I := splitI ibox77 2 66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 false
private noncomputable def ibox79 : Fin 4 → FixedTape.I := splitI ibox78 1 110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 false
private noncomputable def ibox80 : Fin 4 → FixedTape.I := splitI ibox78 1 110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 true
private noncomputable def ibox81 : Fin 4 → FixedTape.I := splitI ibox77 2 66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 true
private noncomputable def ibox82 : Fin 4 → FixedTape.I := splitI ibox81 1 110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 false
private noncomputable def ibox83 : Fin 4 → FixedTape.I := splitI ibox81 1 110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 true
private noncomputable def ibox84 : Fin 4 → FixedTape.I := splitI ibox83 2 77459736118186623216055924496550512509886731323523894997880061975697817600000000000000000000000 false
private noncomputable def ibox85 : Fin 4 → FixedTape.I := splitI ibox83 2 77459736118186623216055924496550512509886731323523894997880061975697817600000000000000000000000 true
private noncomputable def ibox86 : Fin 4 → FixedTape.I := splitI ibox76 1 132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 true
private noncomputable def ibox87 : Fin 4 → FixedTape.I := splitI ibox86 2 66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 false
private noncomputable def ibox88 : Fin 4 → FixedTape.I := splitI ibox87 1 154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 false
private noncomputable def ibox89 : Fin 4 → FixedTape.I := splitI ibox88 1 143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 false
private noncomputable def ibox90 : Fin 4 → FixedTape.I := splitI ibox88 1 143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 true
private noncomputable def ibox91 : Fin 4 → FixedTape.I := splitI ibox90 2 55328382941561873725754231783250366078490522373945639284200044268355584000000000000000000000000 false
private noncomputable def ibox92 : Fin 4 → FixedTape.I := splitI ibox90 2 55328382941561873725754231783250366078490522373945639284200044268355584000000000000000000000000 true
private noncomputable def ibox93 : Fin 4 → FixedTape.I := splitI ibox87 1 154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 true
private noncomputable def ibox94 : Fin 4 → FixedTape.I := splitI ibox93 2 55328382941561873725754231783250366078490522373945639284200044268355584000000000000000000000000 false
private noncomputable def ibox95 : Fin 4 → FixedTape.I := splitI ibox94 1 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 false
private noncomputable def ibox96 : Fin 4 → FixedTape.I := splitI ibox94 1 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 true
private noncomputable def ibox97 : Fin 4 → FixedTape.I := splitI ibox96 0 146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 false
private noncomputable def ibox98 : Fin 4 → FixedTape.I := splitI ibox96 0 146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 true
private noncomputable def ibox99 : Fin 4 → FixedTape.I := splitI ibox93 2 55328382941561873725754231783250366078490522373945639284200044268355584000000000000000000000000 true
private noncomputable def ibox100 : Fin 4 → FixedTape.I := splitI ibox99 1 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 false
private noncomputable def ibox101 : Fin 4 → FixedTape.I := splitI ibox99 1 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 true
private noncomputable def ibox102 : Fin 4 → FixedTape.I := splitI ibox101 0 146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 false
private noncomputable def ibox103 : Fin 4 → FixedTape.I := splitI ibox101 0 146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 true
private noncomputable def ibox104 : Fin 4 → FixedTape.I := splitI ibox86 2 66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 true
private noncomputable def ibox105 : Fin 4 → FixedTape.I := splitI ibox104 1 154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 false
private noncomputable def ibox106 : Fin 4 → FixedTape.I := splitI ibox105 2 77459736118186623216055924496550512509886731323523894997880061975697817600000000000000000000000 false
private noncomputable def ibox107 : Fin 4 → FixedTape.I := splitI ibox105 2 77459736118186623216055924496550512509886731323523894997880061975697817600000000000000000000000 true
private noncomputable def ibox108 : Fin 4 → FixedTape.I := splitI ibox104 1 154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 true
private noncomputable def ibox109 : Fin 4 → FixedTape.I := splitI ibox108 2 77459736118186623216055924496550512509886731323523894997880061975697817600000000000000000000000 false
private noncomputable def ibox110 : Fin 4 → FixedTape.I := splitI ibox109 1 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 false
private noncomputable def ibox111 : Fin 4 → FixedTape.I := splitI ibox109 1 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 true
private noncomputable def ibox112 : Fin 4 → FixedTape.I := splitI ibox108 2 77459736118186623216055924496550512509886731323523894997880061975697817600000000000000000000000 true
private noncomputable def ibox113 : Fin 4 → FixedTape.I := splitI ibox112 1 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 false
private noncomputable def ibox114 : Fin 4 → FixedTape.I := splitI ibox112 1 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 true
private noncomputable def ibox115 : Fin 4 → FixedTape.I := splitI ibox1 2 88525412706498997961206770853200585725584835798313022854720070829368934400000000000000000000000 true
private noncomputable def ibox116 : Fin 4 → FixedTape.I := splitI ibox115 2 132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 false
private noncomputable def ibox117 : Fin 4 → FixedTape.I := splitI ibox116 1 88525412706498997961206770853200585725584835798313022854720070829368934400000000000000000000000 false
private noncomputable def ibox118 : Fin 4 → FixedTape.I := splitI ibox117 2 110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 false
private noncomputable def ibox119 : Fin 4 → FixedTape.I := splitI ibox118 1 44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 false
private noncomputable def ibox120 : Fin 4 → FixedTape.I := splitI ibox119 2 99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 false
private noncomputable def ibox121 : Fin 4 → FixedTape.I := splitI ibox119 2 99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 true
private noncomputable def ibox122 : Fin 4 → FixedTape.I := splitI ibox118 1 44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 true
private noncomputable def ibox123 : Fin 4 → FixedTape.I := splitI ibox122 2 99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 false
private noncomputable def ibox124 : Fin 4 → FixedTape.I := splitI ibox122 2 99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 true
private noncomputable def ibox125 : Fin 4 → FixedTape.I := splitI ibox117 2 110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 true
private noncomputable def ibox126 : Fin 4 → FixedTape.I := splitI ibox125 1 44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 false
private noncomputable def ibox127 : Fin 4 → FixedTape.I := splitI ibox126 2 121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 false
private noncomputable def ibox128 : Fin 4 → FixedTape.I := splitI ibox126 2 121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 true
private noncomputable def ibox129 : Fin 4 → FixedTape.I := splitI ibox125 1 44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 true
private noncomputable def ibox130 : Fin 4 → FixedTape.I := splitI ibox129 2 121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 false
private noncomputable def ibox131 : Fin 4 → FixedTape.I := splitI ibox129 2 121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 true
private noncomputable def ibox132 : Fin 4 → FixedTape.I := splitI ibox116 1 88525412706498997961206770853200585725584835798313022854720070829368934400000000000000000000000 true
private noncomputable def ibox133 : Fin 4 → FixedTape.I := splitI ibox132 1 132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 false
private noncomputable def ibox134 : Fin 4 → FixedTape.I := splitI ibox133 2 110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 false
private noncomputable def ibox135 : Fin 4 → FixedTape.I := splitI ibox134 2 99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 false
private noncomputable def ibox136 : Fin 4 → FixedTape.I := splitI ibox135 1 110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 false
private noncomputable def ibox137 : Fin 4 → FixedTape.I := splitI ibox135 1 110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 true
private noncomputable def ibox138 : Fin 4 → FixedTape.I := splitI ibox134 2 99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 true
private noncomputable def ibox139 : Fin 4 → FixedTape.I := splitI ibox138 1 110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 false
private noncomputable def ibox140 : Fin 4 → FixedTape.I := splitI ibox138 1 110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 true
private noncomputable def ibox141 : Fin 4 → FixedTape.I := splitI ibox133 2 110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 true
private noncomputable def ibox142 : Fin 4 → FixedTape.I := splitI ibox141 2 121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 false
private noncomputable def ibox143 : Fin 4 → FixedTape.I := splitI ibox141 2 121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 true
private noncomputable def ibox144 : Fin 4 → FixedTape.I := splitI ibox132 1 132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 true
private noncomputable def ibox145 : Fin 4 → FixedTape.I := splitI ibox144 2 110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 false
private noncomputable def ibox146 : Fin 4 → FixedTape.I := splitI ibox145 1 154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 false
private noncomputable def ibox147 : Fin 4 → FixedTape.I := splitI ibox146 2 99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 false
private noncomputable def ibox148 : Fin 4 → FixedTape.I := splitI ibox146 2 99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 true
private noncomputable def ibox149 : Fin 4 → FixedTape.I := splitI ibox145 1 154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 true
private noncomputable def ibox150 : Fin 4 → FixedTape.I := splitI ibox149 2 99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 false
private noncomputable def ibox151 : Fin 4 → FixedTape.I := splitI ibox150 1 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 false
private noncomputable def ibox152 : Fin 4 → FixedTape.I := splitI ibox150 1 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 true
private noncomputable def ibox153 : Fin 4 → FixedTape.I := splitI ibox149 2 99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 true
private noncomputable def ibox154 : Fin 4 → FixedTape.I := splitI ibox153 1 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 false
private noncomputable def ibox155 : Fin 4 → FixedTape.I := splitI ibox153 1 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 true
private noncomputable def ibox156 : Fin 4 → FixedTape.I := splitI ibox144 2 110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 true
private noncomputable def ibox157 : Fin 4 → FixedTape.I := splitI ibox156 1 154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 false
private noncomputable def ibox158 : Fin 4 → FixedTape.I := splitI ibox157 2 121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 false
private noncomputable def ibox159 : Fin 4 → FixedTape.I := splitI ibox157 2 121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 true
private noncomputable def ibox160 : Fin 4 → FixedTape.I := splitI ibox156 1 154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 true
private noncomputable def ibox161 : Fin 4 → FixedTape.I := splitI ibox160 2 121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 false
private noncomputable def ibox162 : Fin 4 → FixedTape.I := splitI ibox161 1 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 false
private noncomputable def ibox163 : Fin 4 → FixedTape.I := splitI ibox161 1 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 true
private noncomputable def ibox164 : Fin 4 → FixedTape.I := splitI ibox160 2 121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 true
private noncomputable def ibox165 : Fin 4 → FixedTape.I := splitI ibox115 2 132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 true
private noncomputable def ibox166 : Fin 4 → FixedTape.I := splitI ibox165 1 88525412706498997961206770853200585725584835798313022854720070829368934400000000000000000000000 false
private noncomputable def ibox167 : Fin 4 → FixedTape.I := splitI ibox166 2 154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 false
private noncomputable def ibox168 : Fin 4 → FixedTape.I := splitI ibox167 2 143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 false
private noncomputable def ibox169 : Fin 4 → FixedTape.I := splitI ibox168 1 44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 false
private noncomputable def ibox170 : Fin 4 → FixedTape.I := splitI ibox168 1 44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 true
private noncomputable def ibox171 : Fin 4 → FixedTape.I := splitI ibox167 2 143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 true
private noncomputable def ibox172 : Fin 4 → FixedTape.I := splitI ibox171 1 44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 false
private noncomputable def ibox173 : Fin 4 → FixedTape.I := splitI ibox171 1 44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 true
private noncomputable def ibox174 : Fin 4 → FixedTape.I := splitI ibox166 2 154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 true
private noncomputable def ibox175 : Fin 4 → FixedTape.I := splitI ibox174 2 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 false
private noncomputable def ibox176 : Fin 4 → FixedTape.I := splitI ibox175 1 44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 false
private noncomputable def ibox177 : Fin 4 → FixedTape.I := splitI ibox175 1 44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 true
private noncomputable def ibox178 : Fin 4 → FixedTape.I := splitI ibox174 2 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 true
private noncomputable def ibox179 : Fin 4 → FixedTape.I := splitI ibox165 1 88525412706498997961206770853200585725584835798313022854720070829368934400000000000000000000000 true
private noncomputable def ibox180 : Fin 4 → FixedTape.I := splitI ibox179 2 154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 false
private noncomputable def ibox181 : Fin 4 → FixedTape.I := splitI ibox180 1 132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 false
private noncomputable def ibox182 : Fin 4 → FixedTape.I := splitI ibox181 2 143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 false
private noncomputable def ibox183 : Fin 4 → FixedTape.I := splitI ibox181 2 143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 true
private noncomputable def ibox184 : Fin 4 → FixedTape.I := splitI ibox180 1 132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 true
private noncomputable def ibox185 : Fin 4 → FixedTape.I := splitI ibox184 2 143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 false
private noncomputable def ibox186 : Fin 4 → FixedTape.I := splitI ibox185 1 154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 false
private noncomputable def ibox187 : Fin 4 → FixedTape.I := splitI ibox185 1 154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 true
private noncomputable def ibox188 : Fin 4 → FixedTape.I := splitI ibox184 2 143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 true
private noncomputable def ibox189 : Fin 4 → FixedTape.I := faceI ibox188 2 false
private noncomputable def ibox190 : Fin 4 → FixedTape.I := splitI ibox179 2 154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 true
private noncomputable def ibox191 : Fin 4 → FixedTape.I := splitI ibox190 1 132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 false
private noncomputable def ibox192 : Fin 4 → FixedTape.I := splitI ibox191 2 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 false
private noncomputable def ibox193 : Fin 4 → FixedTape.I := splitI ibox191 2 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 true
private noncomputable def ibox194 : Fin 4 → FixedTape.I := splitI ibox190 1 132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 true
private noncomputable def ibox195 : Fin 4 → FixedTape.I := splitI ibox194 2 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 false
private noncomputable def ibox196 : Fin 4 → FixedTape.I := faceI ibox195 2 false
private noncomputable def ibox197 : Fin 4 → FixedTape.I := splitI ibox194 2 165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 true
private noncomputable def ibox198 : Fin 4 → FixedTape.I := faceI ibox197 2 false
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
private noncomputable def tree196 : TapeTree := .centered (candidateRows ibox196) (candidateRows (FixedTape.midBox ibox196))
attribute [irreducible] tree196
private theorem sign_196 : 2*denominator*(computed denominator (FixedTape.midBox ibox196)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox196).gradient k).lo.natAbs ((computed denominator ibox196).gradient k).hi.natAbs : Int)*((ibox196 k).hi-(ibox196 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox196
    (computed denominator ibox196) (computed denominator (FixedTape.midBox ibox196))
    (by decide +kernel)
private theorem midpoint_even_196 : ∀ k, 2 ∣ (ibox196 k).lo+(ibox196 k).hi := by decide +kernel
private theorem accepted_196 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox196) tree196 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox196 midpoint_even_196
  simp only [tree196,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox196,candidate_valid h (FixedTape.midBox ibox196),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox196 113 (FixedTape.rowsAux denominator ibox196 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox196) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_196
private noncomputable def tree195 : TapeTree := .face 2 false (candidateRows ibox195) tree196
attribute [irreducible] tree195
private theorem sign_195 : ((computed denominator ibox195).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_195 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox195) tree195 = true := by
  simp only [tree195,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox195,?_,accepted_196 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox195)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox195).gradient 2).hi) denominator_positive).1 sign_195
private noncomputable def tree194 : TapeTree := .split 2 (((165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree195 tree197
attribute [irreducible] tree194
private theorem accepted_194 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox194) tree194 = true := by
  simp only [tree194,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox194 2 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) false,decode_split denominator ibox194 2 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_195 h,accepted_197 h⟩
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
private noncomputable def tree191 : TapeTree := .split 2 (((165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree192 tree193
attribute [irreducible] tree191
private theorem accepted_191 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox191) tree191 = true := by
  simp only [tree191,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox191 2 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) false,decode_split denominator ibox191 2 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_192 h,accepted_193 h⟩
private noncomputable def tree190 : TapeTree := .split 1 (((132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree191 tree194
attribute [irreducible] tree190
private theorem accepted_190 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox190) tree190 = true := by
  simp only [tree190,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox190 1 (132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 : Int) false,decode_split denominator ibox190 1 (132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_191 h,accepted_194 h⟩
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
private noncomputable def tree188 : TapeTree := .face 2 false (candidateRows ibox188) tree189
attribute [irreducible] tree188
private theorem sign_188 : ((computed denominator ibox188).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_188 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox188) tree188 = true := by
  simp only [tree188,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox188,?_,accepted_189 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox188)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox188).gradient 2).hi) denominator_positive).1 sign_188
private noncomputable def tree187 : TapeTree := .centered (candidateRows ibox187) (candidateRows (FixedTape.midBox ibox187))
attribute [irreducible] tree187
private theorem sign_187 : 2*denominator*(computed denominator (FixedTape.midBox ibox187)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox187).gradient k).lo.natAbs ((computed denominator ibox187).gradient k).hi.natAbs : Int)*((ibox187 k).hi-(ibox187 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox187
    (computed denominator ibox187) (computed denominator (FixedTape.midBox ibox187))
    (by decide +kernel)
private theorem midpoint_even_187 : ∀ k, 2 ∣ (ibox187 k).lo+(ibox187 k).hi := by decide +kernel
private theorem accepted_187 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox187) tree187 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox187 midpoint_even_187
  simp only [tree187,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox187,candidate_valid h (FixedTape.midBox ibox187),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox187 113 (FixedTape.rowsAux denominator ibox187 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox187) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_187
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
private noncomputable def tree185 : TapeTree := .split 1 (((154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree186 tree187
attribute [irreducible] tree185
private theorem accepted_185 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox185) tree185 = true := by
  simp only [tree185,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox185 1 (154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) false,decode_split denominator ibox185 1 (154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_186 h,accepted_187 h⟩
private noncomputable def tree184 : TapeTree := .split 2 (((143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree185 tree188
attribute [irreducible] tree184
private theorem accepted_184 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox184) tree184 = true := by
  simp only [tree184,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox184 2 (143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 : Int) false,decode_split denominator ibox184 2 (143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_185 h,accepted_188 h⟩
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
private noncomputable def tree181 : TapeTree := .split 2 (((143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree182 tree183
attribute [irreducible] tree181
private theorem accepted_181 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox181) tree181 = true := by
  simp only [tree181,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox181 2 (143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 : Int) false,decode_split denominator ibox181 2 (143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_182 h,accepted_183 h⟩
private noncomputable def tree180 : TapeTree := .split 1 (((132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree181 tree184
attribute [irreducible] tree180
private theorem accepted_180 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox180) tree180 = true := by
  simp only [tree180,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox180 1 (132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 : Int) false,decode_split denominator ibox180 1 (132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_181 h,accepted_184 h⟩
private noncomputable def tree179 : TapeTree := .split 2 (((154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree180 tree190
attribute [irreducible] tree179
private theorem accepted_179 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox179) tree179 = true := by
  simp only [tree179,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox179 2 (154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) false,decode_split denominator ibox179 2 (154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_180 h,accepted_190 h⟩
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
private noncomputable def tree175 : TapeTree := .split 1 (((44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree176 tree177
attribute [irreducible] tree175
private theorem accepted_175 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox175) tree175 = true := by
  simp only [tree175,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox175 1 (44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) false,decode_split denominator ibox175 1 (44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_176 h,accepted_177 h⟩
private noncomputable def tree174 : TapeTree := .split 2 (((165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree175 tree178
attribute [irreducible] tree174
private theorem accepted_174 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox174) tree174 = true := by
  simp only [tree174,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox174 2 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) false,decode_split denominator ibox174 2 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_175 h,accepted_178 h⟩
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
private noncomputable def tree171 : TapeTree := .split 1 (((44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree172 tree173
attribute [irreducible] tree171
private theorem accepted_171 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox171) tree171 = true := by
  simp only [tree171,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox171 1 (44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) false,decode_split denominator ibox171 1 (44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_172 h,accepted_173 h⟩
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
private noncomputable def tree168 : TapeTree := .split 1 (((44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree169 tree170
attribute [irreducible] tree168
private theorem accepted_168 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox168) tree168 = true := by
  simp only [tree168,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox168 1 (44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) false,decode_split denominator ibox168 1 (44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_169 h,accepted_170 h⟩
private noncomputable def tree167 : TapeTree := .split 2 (((143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree168 tree171
attribute [irreducible] tree167
private theorem accepted_167 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox167) tree167 = true := by
  simp only [tree167,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox167 2 (143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 : Int) false,decode_split denominator ibox167 2 (143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_168 h,accepted_171 h⟩
private noncomputable def tree166 : TapeTree := .split 2 (((154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree167 tree174
attribute [irreducible] tree166
private theorem accepted_166 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox166) tree166 = true := by
  simp only [tree166,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox166 2 (154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) false,decode_split denominator ibox166 2 (154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_167 h,accepted_174 h⟩
private noncomputable def tree165 : TapeTree := .split 1 (((88525412706498997961206770853200585725584835798313022854720070829368934400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree166 tree179
attribute [irreducible] tree165
private theorem accepted_165 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox165) tree165 = true := by
  simp only [tree165,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox165 1 (88525412706498997961206770853200585725584835798313022854720070829368934400000000000000000000000 : Int) false,decode_split denominator ibox165 1 (88525412706498997961206770853200585725584835798313022854720070829368934400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_166 h,accepted_179 h⟩
private noncomputable def tree164 : TapeTree := .centered (candidateRows ibox164) (candidateRows (FixedTape.midBox ibox164))
attribute [irreducible] tree164
private theorem sign_164 : 2*denominator*(computed denominator (FixedTape.midBox ibox164)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox164).gradient k).lo.natAbs ((computed denominator ibox164).gradient k).hi.natAbs : Int)*((ibox164 k).hi-(ibox164 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox164
    (computed denominator ibox164) (computed denominator (FixedTape.midBox ibox164))
    (by decide +kernel)
private theorem midpoint_even_164 : ∀ k, 2 ∣ (ibox164 k).lo+(ibox164 k).hi := by decide +kernel
private theorem accepted_164 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox164) tree164 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox164 midpoint_even_164
  simp only [tree164,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox164,candidate_valid h (FixedTape.midBox ibox164),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox164 113 (FixedTape.rowsAux denominator ibox164 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox164) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_164
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
private noncomputable def tree161 : TapeTree := .split 1 (((165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree162 tree163
attribute [irreducible] tree161
private theorem accepted_161 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox161) tree161 = true := by
  simp only [tree161,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox161 1 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) false,decode_split denominator ibox161 1 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_162 h,accepted_163 h⟩
private noncomputable def tree160 : TapeTree := .split 2 (((121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree161 tree164
attribute [irreducible] tree160
private theorem accepted_160 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox160) tree160 = true := by
  simp only [tree160,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox160 2 (121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 : Int) false,decode_split denominator ibox160 2 (121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_161 h,accepted_164 h⟩
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
private noncomputable def tree157 : TapeTree := .split 2 (((121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree158 tree159
attribute [irreducible] tree157
private theorem accepted_157 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox157) tree157 = true := by
  simp only [tree157,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox157 2 (121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 : Int) false,decode_split denominator ibox157 2 (121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_158 h,accepted_159 h⟩
private noncomputable def tree156 : TapeTree := .split 1 (((154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree157 tree160
attribute [irreducible] tree156
private theorem accepted_156 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox156) tree156 = true := by
  simp only [tree156,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox156 1 (154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) false,decode_split denominator ibox156 1 (154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_157 h,accepted_160 h⟩
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
private noncomputable def tree153 : TapeTree := .split 1 (((165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree154 tree155
attribute [irreducible] tree153
private theorem accepted_153 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox153) tree153 = true := by
  simp only [tree153,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox153 1 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) false,decode_split denominator ibox153 1 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) true]
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
private noncomputable def tree150 : TapeTree := .split 1 (((165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree151 tree152
attribute [irreducible] tree150
private theorem accepted_150 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox150) tree150 = true := by
  simp only [tree150,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox150 1 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) false,decode_split denominator ibox150 1 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_151 h,accepted_152 h⟩
private noncomputable def tree149 : TapeTree := .split 2 (((99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree150 tree153
attribute [irreducible] tree149
private theorem accepted_149 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox149) tree149 = true := by
  simp only [tree149,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox149 2 (99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 : Int) false,decode_split denominator ibox149 2 (99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_150 h,accepted_153 h⟩
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
private noncomputable def tree146 : TapeTree := .split 2 (((99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree147 tree148
attribute [irreducible] tree146
private theorem accepted_146 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox146) tree146 = true := by
  simp only [tree146,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox146 2 (99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 : Int) false,decode_split denominator ibox146 2 (99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_147 h,accepted_148 h⟩
private noncomputable def tree145 : TapeTree := .split 1 (((154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree146 tree149
attribute [irreducible] tree145
private theorem accepted_145 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox145) tree145 = true := by
  simp only [tree145,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox145 1 (154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) false,decode_split denominator ibox145 1 (154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_146 h,accepted_149 h⟩
private noncomputable def tree144 : TapeTree := .split 2 (((110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree145 tree156
attribute [irreducible] tree144
private theorem accepted_144 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox144) tree144 = true := by
  simp only [tree144,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox144 2 (110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) false,decode_split denominator ibox144 2 (110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_145 h,accepted_156 h⟩
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
private noncomputable def tree141 : TapeTree := .split 2 (((121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree142 tree143
attribute [irreducible] tree141
private theorem accepted_141 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox141) tree141 = true := by
  simp only [tree141,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox141 2 (121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 : Int) false,decode_split denominator ibox141 2 (121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 : Int) true]
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
private noncomputable def tree138 : TapeTree := .split 1 (((110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree139 tree140
attribute [irreducible] tree138
private theorem accepted_138 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox138) tree138 = true := by
  simp only [tree138,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox138 1 (110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) false,decode_split denominator ibox138 1 (110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_139 h,accepted_140 h⟩
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
private noncomputable def tree135 : TapeTree := .split 1 (((110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree136 tree137
attribute [irreducible] tree135
private theorem accepted_135 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox135) tree135 = true := by
  simp only [tree135,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox135 1 (110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) false,decode_split denominator ibox135 1 (110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_136 h,accepted_137 h⟩
private noncomputable def tree134 : TapeTree := .split 2 (((99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree135 tree138
attribute [irreducible] tree134
private theorem accepted_134 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox134) tree134 = true := by
  simp only [tree134,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox134 2 (99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 : Int) false,decode_split denominator ibox134 2 (99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_135 h,accepted_138 h⟩
private noncomputable def tree133 : TapeTree := .split 2 (((110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree134 tree141
attribute [irreducible] tree133
private theorem accepted_133 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox133) tree133 = true := by
  simp only [tree133,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox133 2 (110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) false,decode_split denominator ibox133 2 (110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_134 h,accepted_141 h⟩
private noncomputable def tree132 : TapeTree := .split 1 (((132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree133 tree144
attribute [irreducible] tree132
private theorem accepted_132 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox132) tree132 = true := by
  simp only [tree132,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox132 1 (132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 : Int) false,decode_split denominator ibox132 1 (132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_133 h,accepted_144 h⟩
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
private noncomputable def tree129 : TapeTree := .split 2 (((121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree130 tree131
attribute [irreducible] tree129
private theorem accepted_129 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox129) tree129 = true := by
  simp only [tree129,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox129 2 (121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 : Int) false,decode_split denominator ibox129 2 (121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_130 h,accepted_131 h⟩
private noncomputable def tree128 : TapeTree := .centered (candidateRows ibox128) (candidateRows (FixedTape.midBox ibox128))
attribute [irreducible] tree128
private theorem sign_128 : 2*denominator*(computed denominator (FixedTape.midBox ibox128)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox128).gradient k).lo.natAbs ((computed denominator ibox128).gradient k).hi.natAbs : Int)*((ibox128 k).hi-(ibox128 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox128
    (computed denominator ibox128) (computed denominator (FixedTape.midBox ibox128))
    (by decide +kernel)
private theorem midpoint_even_128 : ∀ k, 2 ∣ (ibox128 k).lo+(ibox128 k).hi := by decide +kernel
private theorem accepted_128 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox128) tree128 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox128 midpoint_even_128
  simp only [tree128,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox128,candidate_valid h (FixedTape.midBox ibox128),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox128 113 (FixedTape.rowsAux denominator ibox128 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox128) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_128
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
private noncomputable def tree126 : TapeTree := .split 2 (((121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree127 tree128
attribute [irreducible] tree126
private theorem accepted_126 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox126) tree126 = true := by
  simp only [tree126,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox126 2 (121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 : Int) false,decode_split denominator ibox126 2 (121722442471436122196659309923150805372679149222680406425240097390382284800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_127 h,accepted_128 h⟩
private noncomputable def tree125 : TapeTree := .split 1 (((44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree126 tree129
attribute [irreducible] tree125
private theorem accepted_125 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox125) tree125 = true := by
  simp only [tree125,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox125 1 (44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) false,decode_split denominator ibox125 1 (44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_126 h,accepted_129 h⟩
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
private noncomputable def tree122 : TapeTree := .split 2 (((99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree123 tree124
attribute [irreducible] tree122
private theorem accepted_122 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox122) tree122 = true := by
  simp only [tree122,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox122 2 (99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 : Int) false,decode_split denominator ibox122 2 (99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_123 h,accepted_124 h⟩
private noncomputable def tree121 : TapeTree := .centered (candidateRows ibox121) (candidateRows (FixedTape.midBox ibox121))
attribute [irreducible] tree121
private theorem sign_121 : 2*denominator*(computed denominator (FixedTape.midBox ibox121)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox121).gradient k).lo.natAbs ((computed denominator ibox121).gradient k).hi.natAbs : Int)*((ibox121 k).hi-(ibox121 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox121
    (computed denominator ibox121) (computed denominator (FixedTape.midBox ibox121))
    (by decide +kernel)
private theorem midpoint_even_121 : ∀ k, 2 ∣ (ibox121 k).lo+(ibox121 k).hi := by decide +kernel
private theorem accepted_121 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox121) tree121 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox121 midpoint_even_121
  simp only [tree121,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox121,candidate_valid h (FixedTape.midBox ibox121),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox121 113 (FixedTape.rowsAux denominator ibox121 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox121) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_121
private noncomputable def tree120 : TapeTree := .centered (candidateRows ibox120) (candidateRows (FixedTape.midBox ibox120))
attribute [irreducible] tree120
private theorem sign_120 : 2*denominator*(computed denominator (FixedTape.midBox ibox120)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox120).gradient k).lo.natAbs ((computed denominator ibox120).gradient k).hi.natAbs : Int)*((ibox120 k).hi-(ibox120 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox120
    (computed denominator ibox120) (computed denominator (FixedTape.midBox ibox120))
    (by decide +kernel)
private theorem midpoint_even_120 : ∀ k, 2 ∣ (ibox120 k).lo+(ibox120 k).hi := by decide +kernel
private theorem accepted_120 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox120) tree120 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox120 midpoint_even_120
  simp only [tree120,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox120,candidate_valid h (FixedTape.midBox ibox120),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox120 113 (FixedTape.rowsAux denominator ibox120 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox120) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_120
private noncomputable def tree119 : TapeTree := .split 2 (((99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree120 tree121
attribute [irreducible] tree119
private theorem accepted_119 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox119) tree119 = true := by
  simp only [tree119,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox119 2 (99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 : Int) false,decode_split denominator ibox119 2 (99591089294811372706357617209850658941282940273102150711560079683040051200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_120 h,accepted_121 h⟩
private noncomputable def tree118 : TapeTree := .split 1 (((44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree119 tree122
attribute [irreducible] tree118
private theorem accepted_118 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox118) tree118 = true := by
  simp only [tree118,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox118 1 (44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) false,decode_split denominator ibox118 1 (44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_119 h,accepted_122 h⟩
private noncomputable def tree117 : TapeTree := .split 2 (((110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree118 tree125
attribute [irreducible] tree117
private theorem accepted_117 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox117) tree117 = true := by
  simp only [tree117,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox117 2 (110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) false,decode_split denominator ibox117 2 (110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_118 h,accepted_125 h⟩
private noncomputable def tree116 : TapeTree := .split 1 (((88525412706498997961206770853200585725584835798313022854720070829368934400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree117 tree132
attribute [irreducible] tree116
private theorem accepted_116 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox116) tree116 = true := by
  simp only [tree116,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox116 1 (88525412706498997961206770853200585725584835798313022854720070829368934400000000000000000000000 : Int) false,decode_split denominator ibox116 1 (88525412706498997961206770853200585725584835798313022854720070829368934400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_117 h,accepted_132 h⟩
private noncomputable def tree115 : TapeTree := .split 2 (((132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree116 tree165
attribute [irreducible] tree115
private theorem accepted_115 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox115) tree115 = true := by
  simp only [tree115,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox115 2 (132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 : Int) false,decode_split denominator ibox115 2 (132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_116 h,accepted_165 h⟩
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
private noncomputable def tree112 : TapeTree := .split 1 (((165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree113 tree114
attribute [irreducible] tree112
private theorem accepted_112 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox112) tree112 = true := by
  simp only [tree112,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox112 1 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) false,decode_split denominator ibox112 1 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) true]
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
private noncomputable def tree109 : TapeTree := .split 1 (((165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree110 tree111
attribute [irreducible] tree109
private theorem accepted_109 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox109) tree109 = true := by
  simp only [tree109,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox109 1 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) false,decode_split denominator ibox109 1 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_110 h,accepted_111 h⟩
private noncomputable def tree108 : TapeTree := .split 2 (((77459736118186623216055924496550512509886731323523894997880061975697817600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree109 tree112
attribute [irreducible] tree108
private theorem accepted_108 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox108) tree108 = true := by
  simp only [tree108,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox108 2 (77459736118186623216055924496550512509886731323523894997880061975697817600000000000000000000000 : Int) false,decode_split denominator ibox108 2 (77459736118186623216055924496550512509886731323523894997880061975697817600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_109 h,accepted_112 h⟩
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
private noncomputable def tree105 : TapeTree := .split 2 (((77459736118186623216055924496550512509886731323523894997880061975697817600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree106 tree107
attribute [irreducible] tree105
private theorem accepted_105 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox105) tree105 = true := by
  simp only [tree105,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox105 2 (77459736118186623216055924496550512509886731323523894997880061975697817600000000000000000000000 : Int) false,decode_split denominator ibox105 2 (77459736118186623216055924496550512509886731323523894997880061975697817600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_106 h,accepted_107 h⟩
private noncomputable def tree104 : TapeTree := .split 1 (((154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree105 tree108
attribute [irreducible] tree104
private theorem accepted_104 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox104) tree104 = true := by
  simp only [tree104,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox104 1 (154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) false,decode_split denominator ibox104 1 (154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_105 h,accepted_108 h⟩
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
private noncomputable def tree101 : TapeTree := .split 0 (((146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree102 tree103
attribute [irreducible] tree101
private theorem accepted_101 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox101) tree101 = true := by
  simp only [tree101,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox101 0 (146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 : Int) false,decode_split denominator ibox101 0 (146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_102 h,accepted_103 h⟩
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
private noncomputable def tree99 : TapeTree := .split 1 (((165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree100 tree101
attribute [irreducible] tree99
private theorem accepted_99 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox99) tree99 = true := by
  simp only [tree99,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox99 1 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) false,decode_split denominator ibox99 1 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_100 h,accepted_101 h⟩
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
private noncomputable def tree96 : TapeTree := .split 0 (((146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree97 tree98
attribute [irreducible] tree96
private theorem accepted_96 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox96) tree96 = true := by
  simp only [tree96,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox96 0 (146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 : Int) false,decode_split denominator ibox96 0 (146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_97 h,accepted_98 h⟩
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
private noncomputable def tree94 : TapeTree := .split 1 (((165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree95 tree96
attribute [irreducible] tree94
private theorem accepted_94 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox94) tree94 = true := by
  simp only [tree94,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox94 1 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) false,decode_split denominator ibox94 1 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_95 h,accepted_96 h⟩
private noncomputable def tree93 : TapeTree := .split 2 (((55328382941561873725754231783250366078490522373945639284200044268355584000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree94 tree99
attribute [irreducible] tree93
private theorem accepted_93 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox93) tree93 = true := by
  simp only [tree93,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox93 2 (55328382941561873725754231783250366078490522373945639284200044268355584000000000000000000000000 : Int) false,decode_split denominator ibox93 2 (55328382941561873725754231783250366078490522373945639284200044268355584000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_94 h,accepted_99 h⟩
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
private noncomputable def tree90 : TapeTree := .split 2 (((55328382941561873725754231783250366078490522373945639284200044268355584000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree91 tree92
attribute [irreducible] tree90
private theorem accepted_90 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox90) tree90 = true := by
  simp only [tree90,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox90 2 (55328382941561873725754231783250366078490522373945639284200044268355584000000000000000000000000 : Int) false,decode_split denominator ibox90 2 (55328382941561873725754231783250366078490522373945639284200044268355584000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_91 h,accepted_92 h⟩
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
private noncomputable def tree88 : TapeTree := .split 1 (((143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree89 tree90
attribute [irreducible] tree88
private theorem accepted_88 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox88) tree88 = true := by
  simp only [tree88,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox88 1 (143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 : Int) false,decode_split denominator ibox88 1 (143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_89 h,accepted_90 h⟩
private noncomputable def tree87 : TapeTree := .split 1 (((154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree88 tree93
attribute [irreducible] tree87
private theorem accepted_87 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox87) tree87 = true := by
  simp only [tree87,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox87 1 (154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) false,decode_split denominator ibox87 1 (154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_88 h,accepted_93 h⟩
private noncomputable def tree86 : TapeTree := .split 2 (((66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree87 tree104
attribute [irreducible] tree86
private theorem accepted_86 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox86) tree86 = true := by
  simp only [tree86,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox86 2 (66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 : Int) false,decode_split denominator ibox86 2 (66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_87 h,accepted_104 h⟩
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
private noncomputable def tree83 : TapeTree := .split 2 (((77459736118186623216055924496550512509886731323523894997880061975697817600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree84 tree85
attribute [irreducible] tree83
private theorem accepted_83 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox83) tree83 = true := by
  simp only [tree83,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox83 2 (77459736118186623216055924496550512509886731323523894997880061975697817600000000000000000000000 : Int) false,decode_split denominator ibox83 2 (77459736118186623216055924496550512509886731323523894997880061975697817600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_84 h,accepted_85 h⟩
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
private noncomputable def tree81 : TapeTree := .split 1 (((110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree82 tree83
attribute [irreducible] tree81
private theorem accepted_81 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox81) tree81 = true := by
  simp only [tree81,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox81 1 (110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) false,decode_split denominator ibox81 1 (110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_82 h,accepted_83 h⟩
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
private noncomputable def tree78 : TapeTree := .split 1 (((110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree79 tree80
attribute [irreducible] tree78
private theorem accepted_78 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox78) tree78 = true := by
  simp only [tree78,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox78 1 (110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) false,decode_split denominator ibox78 1 (110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_79 h,accepted_80 h⟩
private noncomputable def tree77 : TapeTree := .split 2 (((66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree78 tree81
attribute [irreducible] tree77
private theorem accepted_77 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox77) tree77 = true := by
  simp only [tree77,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox77 2 (66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 : Int) false,decode_split denominator ibox77 2 (66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_78 h,accepted_81 h⟩
private noncomputable def tree76 : TapeTree := .split 1 (((132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree77 tree86
attribute [irreducible] tree76
private theorem accepted_76 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox76) tree76 = true := by
  simp only [tree76,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox76 1 (132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 : Int) false,decode_split denominator ibox76 1 (132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_77 h,accepted_86 h⟩
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
private noncomputable def tree73 : TapeTree := .split 0 (((146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree74 tree75
attribute [irreducible] tree73
private theorem accepted_73 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox73) tree73 = true := by
  simp only [tree73,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox73 0 (146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 : Int) false,decode_split denominator ibox73 0 (146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_74 h,accepted_75 h⟩
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
private noncomputable def tree71 : TapeTree := .split 1 (((171517987118841808549838118528076134843320619359231481781020137231902310400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree72 tree73
attribute [irreducible] tree71
private theorem accepted_71 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox71) tree71 = true := by
  simp only [tree71,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox71 1 (171517987118841808549838118528076134843320619359231481781020137231902310400000000000000000000000 : Int) false,decode_split denominator ibox71 1 (171517987118841808549838118528076134843320619359231481781020137231902310400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_72 h,accepted_73 h⟩
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
private noncomputable def tree68 : TapeTree := .face 1 true (candidateRows ibox68) tree69
attribute [irreducible] tree68
private theorem sign_68 : 0 ≤ ((computed denominator ibox68).gradient 1).lo := by decide +kernel
private theorem accepted_68 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox68) tree68 = true := by
  simp only [tree68,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox68,?_,accepted_69 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox68)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox68).gradient 1).lo) denominator_positive).2 sign_68
private noncomputable def tree67 : TapeTree := .split 0 (((146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree68 tree70
attribute [irreducible] tree67
private theorem accepted_67 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox67) tree67 = true := by
  simp only [tree67,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox67 0 (146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 : Int) false,decode_split denominator ibox67 0 (146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_68 h,accepted_70 h⟩
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
private noncomputable def tree65 : TapeTree := .face 1 true (candidateRows ibox65) tree66
attribute [irreducible] tree65
private theorem sign_65 : 0 ≤ ((computed denominator ibox65).gradient 1).lo := by decide +kernel
private theorem accepted_65 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox65) tree65 = true := by
  simp only [tree65,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox65,?_,accepted_66 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox65)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox65).gradient 1).lo) denominator_positive).2 sign_65
private noncomputable def tree64 : TapeTree := .split 1 (((171517987118841808549838118528076134843320619359231481781020137231902310400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree65 tree67
attribute [irreducible] tree64
private theorem accepted_64 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox64) tree64 = true := by
  simp only [tree64,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox64 1 (171517987118841808549838118528076134843320619359231481781020137231902310400000000000000000000000 : Int) false,decode_split denominator ibox64 1 (171517987118841808549838118528076134843320619359231481781020137231902310400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_65 h,accepted_67 h⟩
private noncomputable def tree63 : TapeTree := .split 2 (((33197029764937124235452539069950219647094313424367383570520026561013350400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree64 tree71
attribute [irreducible] tree63
private theorem accepted_63 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox63) tree63 = true := by
  simp only [tree63,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox63 2 (33197029764937124235452539069950219647094313424367383570520026561013350400000000000000000000000 : Int) false,decode_split denominator ibox63 2 (33197029764937124235452539069950219647094313424367383570520026561013350400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_64 h,accepted_71 h⟩
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
private noncomputable def tree61 : TapeTree := .centered (candidateRows ibox61) (candidateRows (FixedTape.midBox ibox61))
attribute [irreducible] tree61
private theorem sign_61 : 2*denominator*(computed denominator (FixedTape.midBox ibox61)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox61).gradient k).lo.natAbs ((computed denominator ibox61).gradient k).hi.natAbs : Int)*((ibox61 k).hi-(ibox61 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox61
    (computed denominator ibox61) (computed denominator (FixedTape.midBox ibox61))
    (by decide +kernel)
private theorem midpoint_even_61 : ∀ k, 2 ∣ (ibox61 k).lo+(ibox61 k).hi := by decide +kernel
private theorem accepted_61 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox61) tree61 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox61 midpoint_even_61
  simp only [tree61,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox61,candidate_valid h (FixedTape.midBox ibox61),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox61 113 (FixedTape.rowsAux denominator ibox61 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox61) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_61
private noncomputable def tree60 : TapeTree := .centered (candidateRows ibox60) (candidateRows (FixedTape.midBox ibox60))
attribute [irreducible] tree60
private theorem sign_60 : 2*denominator*(computed denominator (FixedTape.midBox ibox60)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox60).gradient k).lo.natAbs ((computed denominator ibox60).gradient k).hi.natAbs : Int)*((ibox60 k).hi-(ibox60 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox60
    (computed denominator ibox60) (computed denominator (FixedTape.midBox ibox60))
    (by decide +kernel)
private theorem midpoint_even_60 : ∀ k, 2 ∣ (ibox60 k).lo+(ibox60 k).hi := by decide +kernel
private theorem accepted_60 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox60) tree60 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox60 midpoint_even_60
  simp only [tree60,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox60,candidate_valid h (FixedTape.midBox ibox60),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox60 113 (FixedTape.rowsAux denominator ibox60 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox60) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_60
private noncomputable def tree59 : TapeTree := .split 1 (((160452310530529433804687272171426061627622514884442353924180128378231193600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree60 tree61
attribute [irreducible] tree59
private theorem accepted_59 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox59) tree59 = true := by
  simp only [tree59,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox59 1 (160452310530529433804687272171426061627622514884442353924180128378231193600000000000000000000000 : Int) false,decode_split denominator ibox59 1 (160452310530529433804687272171426061627622514884442353924180128378231193600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_60 h,accepted_61 h⟩
private noncomputable def tree58 : TapeTree := .split 2 (((33197029764937124235452539069950219647094313424367383570520026561013350400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree59 tree62
attribute [irreducible] tree58
private theorem accepted_58 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox58) tree58 = true := by
  simp only [tree58,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox58 2 (33197029764937124235452539069950219647094313424367383570520026561013350400000000000000000000000 : Int) false,decode_split denominator ibox58 2 (33197029764937124235452539069950219647094313424367383570520026561013350400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_59 h,accepted_62 h⟩
private noncomputable def tree57 : TapeTree := .split 1 (((165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree58 tree63
attribute [irreducible] tree57
private theorem accepted_57 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox57) tree57 = true := by
  simp only [tree57,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox57 1 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) false,decode_split denominator ibox57 1 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_58 h,accepted_63 h⟩
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
private noncomputable def tree53 : TapeTree := .split 2 (((16598514882468562117726269534975109823547156712183691785260013280506675200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree54 tree55
attribute [irreducible] tree53
private theorem accepted_53 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox53) tree53 = true := by
  simp only [tree53,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox53 2 (16598514882468562117726269534975109823547156712183691785260013280506675200000000000000000000000 : Int) false,decode_split denominator ibox53 2 (16598514882468562117726269534975109823547156712183691785260013280506675200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_54 h,accepted_55 h⟩
private noncomputable def tree52 : TapeTree := .split 0 (((146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree53 tree56
attribute [irreducible] tree52
private theorem accepted_52 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox52) tree52 = true := by
  simp only [tree52,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox52 0 (146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 : Int) false,decode_split denominator ibox52 0 (146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_53 h,accepted_56 h⟩
private noncomputable def tree51 : TapeTree := .centered (candidateRows ibox51) (candidateRows (FixedTape.midBox ibox51))
attribute [irreducible] tree51
private theorem sign_51 : 2*denominator*(computed denominator (FixedTape.midBox ibox51)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox51).gradient k).lo.natAbs ((computed denominator ibox51).gradient k).hi.natAbs : Int)*((ibox51 k).hi-(ibox51 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox51
    (computed denominator ibox51) (computed denominator (FixedTape.midBox ibox51))
    (by decide +kernel)
private theorem midpoint_even_51 : ∀ k, 2 ∣ (ibox51 k).lo+(ibox51 k).hi := by decide +kernel
private theorem accepted_51 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox51) tree51 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox51 midpoint_even_51
  simp only [tree51,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox51,candidate_valid h (FixedTape.midBox ibox51),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox51 113 (FixedTape.rowsAux denominator ibox51 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox51) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_51
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
private noncomputable def tree48 : TapeTree := .split 2 (((2766419147078093686287711589162518303924526118697281964210002213417779200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree49 tree50
attribute [irreducible] tree48
private theorem accepted_48 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox48) tree48 = true := by
  simp only [tree48,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox48 2 (2766419147078093686287711589162518303924526118697281964210002213417779200000000000000000000000 : Int) false,decode_split denominator ibox48 2 (2766419147078093686287711589162518303924526118697281964210002213417779200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_49 h,accepted_50 h⟩
private noncomputable def tree47 : TapeTree := .split 2 (((5532838294156187372575423178325036607849052237394563928420004426835558400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree48 tree51
attribute [irreducible] tree47
private theorem accepted_47 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox47) tree47 = true := by
  simp only [tree47,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox47 2 (5532838294156187372575423178325036607849052237394563928420004426835558400000000000000000000000 : Int) false,decode_split denominator ibox47 2 (5532838294156187372575423178325036607849052237394563928420004426835558400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_48 h,accepted_51 h⟩
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
private noncomputable def tree45 : TapeTree := .centered (candidateRows ibox45) (candidateRows (FixedTape.midBox ibox45))
attribute [irreducible] tree45
private theorem sign_45 : 2*denominator*(computed denominator (FixedTape.midBox ibox45)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox45).gradient k).lo.natAbs ((computed denominator ibox45).gradient k).hi.natAbs : Int)*((ibox45 k).hi-(ibox45 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox45
    (computed denominator ibox45) (computed denominator (FixedTape.midBox ibox45))
    (by decide +kernel)
private theorem midpoint_even_45 : ∀ k, 2 ∣ (ibox45 k).lo+(ibox45 k).hi := by decide +kernel
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox45 midpoint_even_45
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox45,candidate_valid h (FixedTape.midBox ibox45),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox45 113 (FixedTape.rowsAux denominator ibox45 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox45) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_45
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
private noncomputable def tree43 : TapeTree := .split 2 (((2766419147078093686287711589162518303924526118697281964210002213417779200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree44 tree45
attribute [irreducible] tree43
private theorem accepted_43 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox43) tree43 = true := by
  simp only [tree43,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox43 2 (2766419147078093686287711589162518303924526118697281964210002213417779200000000000000000000000 : Int) false,decode_split denominator ibox43 2 (2766419147078093686287711589162518303924526118697281964210002213417779200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_44 h,accepted_45 h⟩
private noncomputable def tree42 : TapeTree := .split 2 (((5532838294156187372575423178325036607849052237394563928420004426835558400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree43 tree46
attribute [irreducible] tree42
private theorem accepted_42 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox42) tree42 = true := by
  simp only [tree42,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox42 2 (5532838294156187372575423178325036607849052237394563928420004426835558400000000000000000000000 : Int) false,decode_split denominator ibox42 2 (5532838294156187372575423178325036607849052237394563928420004426835558400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_43 h,accepted_46 h⟩
private noncomputable def tree41 : TapeTree := .split 0 (((146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree42 tree47
attribute [irreducible] tree41
private theorem accepted_41 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox41) tree41 = true := by
  simp only [tree41,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox41 0 (146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 : Int) false,decode_split denominator ibox41 0 (146620214795138965373248714225613470107999884290955944103130117311142297600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_42 h,accepted_47 h⟩
private noncomputable def tree40 : TapeTree := .split 2 (((11065676588312374745150846356650073215698104474789127856840008853671116800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree41 tree52
attribute [irreducible] tree40
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox40 2 (11065676588312374745150846356650073215698104474789127856840008853671116800000000000000000000000 : Int) false,decode_split denominator ibox40 2 (11065676588312374745150846356650073215698104474789127856840008853671116800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_41 h,accepted_52 h⟩
private noncomputable def tree39 : TapeTree := .face 1 true (candidateRows ibox39) tree40
attribute [irreducible] tree39
private theorem sign_39 : 0 ≤ ((computed denominator ibox39).gradient 1).lo := by decide +kernel
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox39,?_,accepted_40 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox39)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox39).gradient 1).lo) denominator_positive).2 sign_39
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
private noncomputable def tree37 : TapeTree := .centered (candidateRows ibox37) (candidateRows (FixedTape.midBox ibox37))
attribute [irreducible] tree37
private theorem sign_37 : 2*denominator*(computed denominator (FixedTape.midBox ibox37)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox37).gradient k).lo.natAbs ((computed denominator ibox37).gradient k).hi.natAbs : Int)*((ibox37 k).hi-(ibox37 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox37
    (computed denominator ibox37) (computed denominator (FixedTape.midBox ibox37))
    (by decide +kernel)
private theorem midpoint_even_37 : ∀ k, 2 ∣ (ibox37 k).lo+(ibox37 k).hi := by decide +kernel
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox37 midpoint_even_37
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox37,candidate_valid h (FixedTape.midBox ibox37),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox37 113 (FixedTape.rowsAux denominator ibox37 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox37) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_37
private noncomputable def tree36 : TapeTree := .split 2 (((11065676588312374745150846356650073215698104474789127856840008853671116800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree37 tree38
attribute [irreducible] tree36
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox36 2 (11065676588312374745150846356650073215698104474789127856840008853671116800000000000000000000000 : Int) false,decode_split denominator ibox36 2 (11065676588312374745150846356650073215698104474789127856840008853671116800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_37 h,accepted_38 h⟩
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
private noncomputable def tree34 : TapeTree := .split 1 (((165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree35 tree39
attribute [irreducible] tree34
private theorem accepted_34 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox34) tree34 = true := by
  simp only [tree34,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox34 1 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) false,decode_split denominator ibox34 1 (165985148824685621177262695349751098235471567121836917852600132805066752000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_35 h,accepted_39 h⟩
private noncomputable def tree33 : TapeTree := .split 2 (((22131353176624749490301692713300146431396208949578255713680017707342233600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree34 tree57
attribute [irreducible] tree33
private theorem accepted_33 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox33) tree33 = true := by
  simp only [tree33,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox33 2 (22131353176624749490301692713300146431396208949578255713680017707342233600000000000000000000000 : Int) false,decode_split denominator ibox33 2 (22131353176624749490301692713300146431396208949578255713680017707342233600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_34 h,accepted_57 h⟩
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
private noncomputable def tree30 : TapeTree := .split 1 (((143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree31 tree32
attribute [irreducible] tree30
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox30 1 (143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 : Int) false,decode_split denominator ibox30 1 (143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 : Int) true]
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
private noncomputable def tree27 : TapeTree := .split 1 (((143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree28 tree29
attribute [irreducible] tree27
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox27 1 (143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 : Int) false,decode_split denominator ibox27 1 (143853795648060871686961002636450951804075358172258662138920115097724518400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_28 h,accepted_29 h⟩
private noncomputable def tree26 : TapeTree := .split 2 (((22131353176624749490301692713300146431396208949578255713680017707342233600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree27 tree30
attribute [irreducible] tree26
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox26 2 (22131353176624749490301692713300146431396208949578255713680017707342233600000000000000000000000 : Int) false,decode_split denominator ibox26 2 (22131353176624749490301692713300146431396208949578255713680017707342233600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_27 h,accepted_30 h⟩
private noncomputable def tree25 : TapeTree := .split 1 (((154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree26 tree33
attribute [irreducible] tree25
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox25 1 (154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) false,decode_split denominator ibox25 1 (154919472236373246432111848993101025019773462647047789995760123951395635200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_26 h,accepted_33 h⟩
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
private noncomputable def tree22 : TapeTree := .split 2 (((22131353176624749490301692713300146431396208949578255713680017707342233600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree23 tree24
attribute [irreducible] tree22
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox22 2 (22131353176624749490301692713300146431396208949578255713680017707342233600000000000000000000000 : Int) false,decode_split denominator ibox22 2 (22131353176624749490301692713300146431396208949578255713680017707342233600000000000000000000000 : Int) true]
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
private noncomputable def tree20 : TapeTree := .split 1 (((110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree21 tree22
attribute [irreducible] tree20
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox20 1 (110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) false,decode_split denominator ibox20 1 (110656765883123747451508463566500732156981044747891278568400088536711168000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_21 h,accepted_22 h⟩
private noncomputable def tree19 : TapeTree := .split 1 (((132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree25
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 1 (132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 : Int) false,decode_split denominator ibox19 1 (132788119059748496941810156279800878588377253697469534282080106244053401600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_20 h,accepted_25 h⟩
private noncomputable def tree18 : TapeTree := .split 2 (((44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree19 tree76
attribute [irreducible] tree18
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox18 2 (44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) false,decode_split denominator ibox18 2 (44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_19 h,accepted_76 h⟩
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
private noncomputable def tree15 : TapeTree := .split 1 (((66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree16 tree17
attribute [irreducible] tree15
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox15 1 (66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 : Int) false,decode_split denominator ibox15 1 (66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 : Int) true]
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
private noncomputable def tree13 : TapeTree := .split 2 (((66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree14 tree15
attribute [irreducible] tree13
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox13 2 (66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 : Int) false,decode_split denominator ibox13 2 (66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 : Int) true]
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
private noncomputable def tree10 : TapeTree := .split 2 (((66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree11 tree12
attribute [irreducible] tree10
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox10 2 (66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 : Int) false,decode_split denominator ibox10 2 (66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_11 h,accepted_12 h⟩
private noncomputable def tree9 : TapeTree := .split 1 (((44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree10 tree13
attribute [irreducible] tree9
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox9 1 (44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) false,decode_split denominator ibox9 1 (44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) true]
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
private noncomputable def tree6 : TapeTree := .split 1 (((66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree8
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 1 (66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 : Int) false,decode_split denominator ibox6 1 (66394059529874248470905078139900439294188626848734767141040053122026700800000000000000000000000 : Int) true]
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
private noncomputable def tree4 : TapeTree := .split 1 (((44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree6
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 1 (44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) false,decode_split denominator ibox4 1 (44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_6 h⟩
private noncomputable def tree3 : TapeTree := .split 2 (((44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree9
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 2 (44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) false,decode_split denominator ibox3 2 (44262706353249498980603385426600292862792417899156511427360035414684467200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_9 h⟩
private noncomputable def tree2 : TapeTree := .split 1 (((88525412706498997961206770853200585725584835798313022854720070829368934400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree18
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 1 (88525412706498997961206770853200585725584835798313022854720070829368934400000000000000000000000 : Int) false,decode_split denominator ibox2 1 (88525412706498997961206770853200585725584835798313022854720070829368934400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_18 h⟩
private noncomputable def tree1 : TapeTree := .split 2 (((88525412706498997961206770853200585725584835798313022854720070829368934400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree2 tree115
attribute [irreducible] tree1
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox1 2 (88525412706498997961206770853200585725584835798313022854720070829368934400000000000000000000000 : Int) false,decode_split denominator ibox1 2 (88525412706498997961206770853200585725584835798313022854720070829368934400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_2 h,accepted_115 h⟩
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
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (4114583333333333/5000000000000000 : ℚ) (4166666666666667/5000000000000000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 113 = e123 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (4114583333333333/5000000000000000 : ℚ) (4166666666666667/5000000000000000 : ℚ)) x → eval e123 x ≤ 0 := by
  have hb := h.child_4 tape 113 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell109_high_internal_top

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell109_high_internal_top
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((4114583333333333/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((4166666666666667/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 109 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 109 p)
    (hkb : ((4166666666666667/5000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((4114583333333333/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : bStar < a), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell109_high_internal_top.cell_bound h.child_8 h.child_9 (Cell109_high_internal_top.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell109_high_internal_top
