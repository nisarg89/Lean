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
namespace Cell121_high_internal_top
private noncomputable def qValues : Fin 2 → ℚ := ![(43956361335054991035054497201740176967/8308785745345758523486681049347789173 : ℚ),(-33780141597749334838940000000000000000/8308785745345758523486681049347789173 : ℚ)]
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
    priceLambda 121 p = ((43956361335054991035054497201740176967/8308785745345758523486681049347789173 : ℝ)+(-33780141597749334838940000000000000000/8308785745345758523486681049347789173 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell121,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 121 p = 0 := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell121,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e123 x = (x 0*(1-x 0))*(aPoint x+priceLambda 121 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 121 (x 0)*psiStar (rPoint x)+(cStar-aPoint x-eta (0 : Fin 9)*psiStar (aPoint x))-(cStar-capPoint x-eta (0 : Fin 9)*psiStar (capPoint x))) := by
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
    (hL : lambdaStar (x 0) = priceLambda 121 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 121 (x 0)) :
    (1)*eval e123 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_neg (not_le.mpr ha),if_neg (not_le.mpr hA),hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (4739583333333333/5000000000000000 : ℚ) (4395636133505499103505449720174017696700000/4587050499937430843922117419533744845930749 : ℚ)) x → eval e123 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((4739583333333333/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((4395636133505499103505449720174017696700000/4587050499937430843922117419533744845930749 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 121 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 121 p)
    (hkb : ((4395636133505499103505449720174017696700000/4587050499937430843922117419533744845930749 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((4739583333333333/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : bStar < a) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h7 (4739583333333333/5000000000000000 : ℚ) (4395636133505499103505449720174017696700000/4587050499937430843922117419533744845930749 : ℚ) bStar p a A r hpcell hkb hr.2 hap hcase hpA hAr
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 121 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 121 (x 0) := by simpa only [hxp] using hT
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
.const (43956361335054991035054497201740176967/8308785745345758523486681049347789173 : ℚ),
.const (-33780141597749334838940000000000000000/8308785745345758523486681049347789173 : ℚ),
.mul 104 1,
.add 103 105,
.mul 1 10,
.add 8 38,
.neg 55,
.add 108 109,
.mul 110 107,
.mul 106 102,
.add 111 112]
private noncomputable def ssaQVals : Fin 15 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(-2840189/5000000 : ℚ),(113609/200000 : ℚ),(1085/4818 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ),(4818/3733 : ℚ),(145513/100000 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(43956361335054991035054497201740176967/8308785745345758523486681049347789173 : ℚ),(-33780141597749334838940000000000000000/8308785745345758523486681049347789173 : ℚ)]
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
private noncomputable def denominator : Int := 1810315192841552741327946724906589150509139857068619979368958743890179642089124187580918516675839460048234501216665600000000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨1716027943214388415362769976880854877057007162407019321500835004737900827799732710132436204657360316109487842555666930117699918888960000000,1734772022849290214290692154311973228169609521147298180779081241190475986864244035471164015876648890867887636480000000000000000000000000000⟩,⟨0,1810315192841552741327946724906589150509139857068619979368958743890179642089124187580918516675839460048234501216665600000000000000000000000⟩,⟨0,1810315192841552741327946724906589150509139857068619979368958743890179642089124187580918516675839460048234501216665600000000000000000000000⟩,⟨0,1810315192841552741327946724906589150509139857068619979368958743890179642089124187580918516675839460048234501216665600000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 3 true
private noncomputable def ibox2 : Fin 4 → FixedTape.I := splitI ibox1 1 905157596420776370663973362453294575254569928534309989684479371945089821044562093790459258337919730024117250608332800000000000000000000000 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 2 905157596420776370663973362453294575254569928534309989684479371945089821044562093790459258337919730024117250608332800000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 2 452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox4 2 452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 true
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox3 1 452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 true
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox7 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox8 2 452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 false
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox8 2 452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 true
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox7 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox11 1 678868197315582277997980021839970931440927446400732492263359528958817365783421570342844443753439797518087937956249600000000000000000000000 false
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox11 1 678868197315582277997980021839970931440927446400732492263359528958817365783421570342844443753439797518087937956249600000000000000000000000 true
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox2 2 905157596420776370663973362453294575254569928534309989684479371945089821044562093790459258337919730024117250608332800000000000000000000000 true
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox14 1 452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 false
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox15 2 1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 false
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox16 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox15 2 1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox19 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox14 1 452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 true
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox22 2 1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 false
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox23 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox23 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox22 2 1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 true
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox26 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox26 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox1 1 905157596420776370663973362453294575254569928534309989684479371945089821044562093790459258337919730024117250608332800000000000000000000000 true
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox29 1 1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 false
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox30 2 905157596420776370663973362453294575254569928534309989684479371945089821044562093790459258337919730024117250608332800000000000000000000000 false
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox31 2 452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 false
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox32 1 1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 false
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox32 1 1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 true
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox31 2 452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 true
private noncomputable def ibox36 : Fin 4 → FixedTape.I := splitI ibox35 1 1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 false
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox35 1 1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 true
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox37 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox37 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox30 2 905157596420776370663973362453294575254569928534309989684479371945089821044562093790459258337919730024117250608332800000000000000000000000 true
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox40 2 1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 false
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox41 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox42 1 1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 false
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox42 1 1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 true
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox41 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox45 1 1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 false
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox45 1 1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 true
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox40 2 1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 true
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox48 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox49 1 1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 false
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox49 1 1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 true
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox48 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox52 1 1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 false
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox52 1 1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 true
private noncomputable def ibox55 : Fin 4 → FixedTape.I := splitI ibox29 1 1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 true
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox55 2 905157596420776370663973362453294575254569928534309989684479371945089821044562093790459258337919730024117250608332800000000000000000000000 false
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox56 1 1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 false
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox57 2 452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 false
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox58 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox58 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox61 : Fin 4 → FixedTape.I := splitI ibox57 2 452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 true
private noncomputable def ibox62 : Fin 4 → FixedTape.I := splitI ibox61 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox63 : Fin 4 → FixedTape.I := splitI ibox61 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox64 : Fin 4 → FixedTape.I := splitI ibox56 1 1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 true
private noncomputable def ibox65 : Fin 4 → FixedTape.I := splitI ibox64 2 452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 false
private noncomputable def ibox66 : Fin 4 → FixedTape.I := splitI ibox65 1 1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 false
private noncomputable def ibox67 : Fin 4 → FixedTape.I := splitI ibox66 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox68 : Fin 4 → FixedTape.I := splitI ibox67 2 226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 false
private noncomputable def ibox69 : Fin 4 → FixedTape.I := splitI ibox67 2 226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 true
private noncomputable def ibox70 : Fin 4 → FixedTape.I := splitI ibox66 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox71 : Fin 4 → FixedTape.I := splitI ibox70 1 1640598143512657171828451719446596417648907995468436856303118861650475300643268794995207405737479510668712516727603200000000000000000000000 false
private noncomputable def ibox72 : Fin 4 → FixedTape.I := splitI ibox70 1 1640598143512657171828451719446596417648907995468436856303118861650475300643268794995207405737479510668712516727603200000000000000000000000 true
private noncomputable def ibox73 : Fin 4 → FixedTape.I := splitI ibox65 1 1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 true
private noncomputable def ibox74 : Fin 4 → FixedTape.I := splitI ibox73 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox75 : Fin 4 → FixedTape.I := splitI ibox74 1 1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 false
private noncomputable def ibox76 : Fin 4 → FixedTape.I := splitI ibox75 2 226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 false
private noncomputable def ibox77 : Fin 4 → FixedTape.I := splitI ibox75 2 226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 true
private noncomputable def ibox78 : Fin 4 → FixedTape.I := splitI ibox74 1 1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 true
private noncomputable def ibox79 : Fin 4 → FixedTape.I := splitI ibox78 2 226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 false
private noncomputable def ibox80 : Fin 4 → FixedTape.I := splitI ibox79 1 1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 false
private noncomputable def ibox81 : Fin 4 → FixedTape.I := faceI ibox80 1 true
private noncomputable def ibox82 : Fin 4 → FixedTape.I := splitI ibox79 1 1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 true
private noncomputable def ibox83 : Fin 4 → FixedTape.I := faceI ibox82 1 true
private noncomputable def ibox84 : Fin 4 → FixedTape.I := splitI ibox83 2 113144699552597046332996670306661821906821241066788748710559921493136227630570261723807407292239966253014656326041600000000000000000000000 false
private noncomputable def ibox85 : Fin 4 → FixedTape.I := splitI ibox84 0 1720713963123113865094750521238634464835157752092089036320396563851044617565860541467118157462182459799087791036750197588274939166720000000 false
private noncomputable def ibox86 : Fin 4 → FixedTape.I := splitI ibox84 0 1720713963123113865094750521238634464835157752092089036320396563851044617565860541467118157462182459799087791036750197588274939166720000000 true
private noncomputable def ibox87 : Fin 4 → FixedTape.I := splitI ibox83 2 113144699552597046332996670306661821906821241066788748710559921493136227630570261723807407292239966253014656326041600000000000000000000000 true
private noncomputable def ibox88 : Fin 4 → FixedTape.I := splitI ibox78 2 226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 true
private noncomputable def ibox89 : Fin 4 → FixedTape.I := splitI ibox88 1 1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 false
private noncomputable def ibox90 : Fin 4 → FixedTape.I := splitI ibox88 1 1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 true
private noncomputable def ibox91 : Fin 4 → FixedTape.I := splitI ibox90 2 339434098657791138998990010919985465720463723200366246131679764479408682891710785171422221876719898759043968978124800000000000000000000000 false
private noncomputable def ibox92 : Fin 4 → FixedTape.I := splitI ibox90 2 339434098657791138998990010919985465720463723200366246131679764479408682891710785171422221876719898759043968978124800000000000000000000000 true
private noncomputable def ibox93 : Fin 4 → FixedTape.I := splitI ibox73 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox94 : Fin 4 → FixedTape.I := splitI ibox93 1 1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 false
private noncomputable def ibox95 : Fin 4 → FixedTape.I := splitI ibox94 2 226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 false
private noncomputable def ibox96 : Fin 4 → FixedTape.I := splitI ibox94 2 226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 true
private noncomputable def ibox97 : Fin 4 → FixedTape.I := splitI ibox93 1 1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 true
private noncomputable def ibox98 : Fin 4 → FixedTape.I := splitI ibox97 2 226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 false
private noncomputable def ibox99 : Fin 4 → FixedTape.I := splitI ibox98 1 1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 false
private noncomputable def ibox100 : Fin 4 → FixedTape.I := faceI ibox99 1 true
private noncomputable def ibox101 : Fin 4 → FixedTape.I := splitI ibox98 1 1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 true
private noncomputable def ibox102 : Fin 4 → FixedTape.I := faceI ibox101 1 true
private noncomputable def ibox103 : Fin 4 → FixedTape.I := splitI ibox102 2 113144699552597046332996670306661821906821241066788748710559921493136227630570261723807407292239966253014656326041600000000000000000000000 false
private noncomputable def ibox104 : Fin 4 → FixedTape.I := splitI ibox103 0 1730086002940564764558711609954193640391458931462228465959519682077332197098116204136482063071826747178287687998916732529424979722240000000 false
private noncomputable def ibox105 : Fin 4 → FixedTape.I := splitI ibox103 0 1730086002940564764558711609954193640391458931462228465959519682077332197098116204136482063071826747178287687998916732529424979722240000000 true
private noncomputable def ibox106 : Fin 4 → FixedTape.I := splitI ibox102 2 113144699552597046332996670306661821906821241066788748710559921493136227630570261723807407292239966253014656326041600000000000000000000000 true
private noncomputable def ibox107 : Fin 4 → FixedTape.I := splitI ibox97 2 226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 true
private noncomputable def ibox108 : Fin 4 → FixedTape.I := splitI ibox107 1 1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 false
private noncomputable def ibox109 : Fin 4 → FixedTape.I := splitI ibox107 1 1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 true
private noncomputable def ibox110 : Fin 4 → FixedTape.I := splitI ibox109 2 339434098657791138998990010919985465720463723200366246131679764479408682891710785171422221876719898759043968978124800000000000000000000000 false
private noncomputable def ibox111 : Fin 4 → FixedTape.I := splitI ibox109 2 339434098657791138998990010919985465720463723200366246131679764479408682891710785171422221876719898759043968978124800000000000000000000000 true
private noncomputable def ibox112 : Fin 4 → FixedTape.I := splitI ibox64 2 452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 true
private noncomputable def ibox113 : Fin 4 → FixedTape.I := splitI ibox112 1 1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 false
private noncomputable def ibox114 : Fin 4 → FixedTape.I := splitI ibox113 2 678868197315582277997980021839970931440927446400732492263359528958817365783421570342844443753439797518087937956249600000000000000000000000 false
private noncomputable def ibox115 : Fin 4 → FixedTape.I := splitI ibox114 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox116 : Fin 4 → FixedTape.I := splitI ibox114 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox117 : Fin 4 → FixedTape.I := splitI ibox113 2 678868197315582277997980021839970931440927446400732492263359528958817365783421570342844443753439797518087937956249600000000000000000000000 true
private noncomputable def ibox118 : Fin 4 → FixedTape.I := splitI ibox117 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox119 : Fin 4 → FixedTape.I := splitI ibox117 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox120 : Fin 4 → FixedTape.I := splitI ibox112 1 1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 true
private noncomputable def ibox121 : Fin 4 → FixedTape.I := splitI ibox120 2 678868197315582277997980021839970931440927446400732492263359528958817365783421570342844443753439797518087937956249600000000000000000000000 false
private noncomputable def ibox122 : Fin 4 → FixedTape.I := splitI ibox121 1 1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 false
private noncomputable def ibox123 : Fin 4 → FixedTape.I := splitI ibox122 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox124 : Fin 4 → FixedTape.I := splitI ibox122 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox125 : Fin 4 → FixedTape.I := splitI ibox121 1 1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 true
private noncomputable def ibox126 : Fin 4 → FixedTape.I := splitI ibox125 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox127 : Fin 4 → FixedTape.I := splitI ibox126 2 565723497762985231664983351533309109534106205333943743552799607465681138152851308619037036461199831265073281630208000000000000000000000000 false
private noncomputable def ibox128 : Fin 4 → FixedTape.I := splitI ibox126 2 565723497762985231664983351533309109534106205333943743552799607465681138152851308619037036461199831265073281630208000000000000000000000000 true
private noncomputable def ibox129 : Fin 4 → FixedTape.I := splitI ibox125 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox130 : Fin 4 → FixedTape.I := splitI ibox129 1 1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 false
private noncomputable def ibox131 : Fin 4 → FixedTape.I := splitI ibox129 1 1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 true
private noncomputable def ibox132 : Fin 4 → FixedTape.I := splitI ibox120 2 678868197315582277997980021839970931440927446400732492263359528958817365783421570342844443753439797518087937956249600000000000000000000000 true
private noncomputable def ibox133 : Fin 4 → FixedTape.I := splitI ibox132 1 1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 false
private noncomputable def ibox134 : Fin 4 → FixedTape.I := splitI ibox133 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox135 : Fin 4 → FixedTape.I := splitI ibox133 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox136 : Fin 4 → FixedTape.I := splitI ibox132 1 1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 true
private noncomputable def ibox137 : Fin 4 → FixedTape.I := splitI ibox136 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox138 : Fin 4 → FixedTape.I := splitI ibox136 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox139 : Fin 4 → FixedTape.I := splitI ibox55 2 905157596420776370663973362453294575254569928534309989684479371945089821044562093790459258337919730024117250608332800000000000000000000000 true
private noncomputable def ibox140 : Fin 4 → FixedTape.I := splitI ibox139 1 1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 false
private noncomputable def ibox141 : Fin 4 → FixedTape.I := splitI ibox140 2 1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 false
private noncomputable def ibox142 : Fin 4 → FixedTape.I := splitI ibox141 2 1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 false
private noncomputable def ibox143 : Fin 4 → FixedTape.I := splitI ibox142 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox144 : Fin 4 → FixedTape.I := splitI ibox142 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox145 : Fin 4 → FixedTape.I := splitI ibox141 2 1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 true
private noncomputable def ibox146 : Fin 4 → FixedTape.I := splitI ibox145 1 1470881094183761602328956713986603684788676133868253733237278979410770959197413402409496294799119561289190532238540800000000000000000000000 false
private noncomputable def ibox147 : Fin 4 → FixedTape.I := splitI ibox145 1 1470881094183761602328956713986603684788676133868253733237278979410770959197413402409496294799119561289190532238540800000000000000000000000 true
private noncomputable def ibox148 : Fin 4 → FixedTape.I := splitI ibox140 2 1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 true
private noncomputable def ibox149 : Fin 4 → FixedTape.I := splitI ibox148 2 1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 false
private noncomputable def ibox150 : Fin 4 → FixedTape.I := splitI ibox149 1 1470881094183761602328956713986603684788676133868253733237278979410770959197413402409496294799119561289190532238540800000000000000000000000 false
private noncomputable def ibox151 : Fin 4 → FixedTape.I := splitI ibox149 1 1470881094183761602328956713986603684788676133868253733237278979410770959197413402409496294799119561289190532238540800000000000000000000000 true
private noncomputable def ibox152 : Fin 4 → FixedTape.I := splitI ibox148 2 1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 true
private noncomputable def ibox153 : Fin 4 → FixedTape.I := splitI ibox152 1 1470881094183761602328956713986603684788676133868253733237278979410770959197413402409496294799119561289190532238540800000000000000000000000 false
private noncomputable def ibox154 : Fin 4 → FixedTape.I := splitI ibox152 1 1470881094183761602328956713986603684788676133868253733237278979410770959197413402409496294799119561289190532238540800000000000000000000000 true
private noncomputable def ibox155 : Fin 4 → FixedTape.I := splitI ibox154 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox156 : Fin 4 → FixedTape.I := splitI ibox154 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox157 : Fin 4 → FixedTape.I := splitI ibox139 1 1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 true
private noncomputable def ibox158 : Fin 4 → FixedTape.I := splitI ibox157 2 1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 false
private noncomputable def ibox159 : Fin 4 → FixedTape.I := splitI ibox158 1 1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 false
private noncomputable def ibox160 : Fin 4 → FixedTape.I := splitI ibox159 2 1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 false
private noncomputable def ibox161 : Fin 4 → FixedTape.I := splitI ibox160 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox162 : Fin 4 → FixedTape.I := splitI ibox160 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox163 : Fin 4 → FixedTape.I := splitI ibox159 2 1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 true
private noncomputable def ibox164 : Fin 4 → FixedTape.I := splitI ibox163 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox165 : Fin 4 → FixedTape.I := splitI ibox163 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox166 : Fin 4 → FixedTape.I := splitI ibox158 1 1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 true
private noncomputable def ibox167 : Fin 4 → FixedTape.I := splitI ibox166 2 1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 false
private noncomputable def ibox168 : Fin 4 → FixedTape.I := splitI ibox167 1 1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 false
private noncomputable def ibox169 : Fin 4 → FixedTape.I := splitI ibox168 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox170 : Fin 4 → FixedTape.I := splitI ibox168 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox171 : Fin 4 → FixedTape.I := splitI ibox167 1 1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 true
private noncomputable def ibox172 : Fin 4 → FixedTape.I := splitI ibox171 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox173 : Fin 4 → FixedTape.I := splitI ibox171 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox174 : Fin 4 → FixedTape.I := splitI ibox166 2 1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 true
private noncomputable def ibox175 : Fin 4 → FixedTape.I := splitI ibox174 1 1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 false
private noncomputable def ibox176 : Fin 4 → FixedTape.I := splitI ibox175 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox177 : Fin 4 → FixedTape.I := splitI ibox175 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox178 : Fin 4 → FixedTape.I := splitI ibox174 1 1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 true
private noncomputable def ibox179 : Fin 4 → FixedTape.I := splitI ibox178 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox180 : Fin 4 → FixedTape.I := splitI ibox178 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox181 : Fin 4 → FixedTape.I := splitI ibox157 2 1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 true
private noncomputable def ibox182 : Fin 4 → FixedTape.I := splitI ibox181 1 1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 false
private noncomputable def ibox183 : Fin 4 → FixedTape.I := splitI ibox182 2 1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 false
private noncomputable def ibox184 : Fin 4 → FixedTape.I := splitI ibox183 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox185 : Fin 4 → FixedTape.I := splitI ibox183 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox186 : Fin 4 → FixedTape.I := splitI ibox182 2 1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 true
private noncomputable def ibox187 : Fin 4 → FixedTape.I := splitI ibox186 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox188 : Fin 4 → FixedTape.I := splitI ibox186 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox189 : Fin 4 → FixedTape.I := splitI ibox181 1 1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 true
private noncomputable def ibox190 : Fin 4 → FixedTape.I := splitI ibox189 2 1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 false
private noncomputable def ibox191 : Fin 4 → FixedTape.I := splitI ibox190 1 1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 false
private noncomputable def ibox192 : Fin 4 → FixedTape.I := splitI ibox191 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox193 : Fin 4 → FixedTape.I := splitI ibox191 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox194 : Fin 4 → FixedTape.I := splitI ibox190 1 1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 true
private noncomputable def ibox195 : Fin 4 → FixedTape.I := splitI ibox194 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox196 : Fin 4 → FixedTape.I := splitI ibox194 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox197 : Fin 4 → FixedTape.I := splitI ibox189 2 1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 true
private noncomputable def ibox198 : Fin 4 → FixedTape.I := splitI ibox197 1 1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 false
private noncomputable def ibox199 : Fin 4 → FixedTape.I := splitI ibox198 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 false
private noncomputable def ibox200 : Fin 4 → FixedTape.I := splitI ibox198 0 1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 true
private noncomputable def ibox201 : Fin 4 → FixedTape.I := splitI ibox197 1 1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 true
private noncomputable def ibox202 : Fin 4 → FixedTape.I := splitI ibox201 2 1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 false
private noncomputable def ibox203 : Fin 4 → FixedTape.I := splitI ibox201 2 1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 true
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
private noncomputable def tree201 : TapeTree := .split 2 (((1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree202 tree203
attribute [irreducible] tree201
private theorem accepted_201 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox201) tree201 = true := by
  simp only [tree201,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox201 2 (1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 : Int) false,decode_split denominator ibox201 2 (1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 : Int) true]
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
private noncomputable def tree198 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree199 tree200
attribute [irreducible] tree198
private theorem accepted_198 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox198) tree198 = true := by
  simp only [tree198,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox198 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox198 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_199 h,accepted_200 h⟩
private noncomputable def tree197 : TapeTree := .split 1 (((1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree198 tree201
attribute [irreducible] tree197
private theorem accepted_197 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox197) tree197 = true := by
  simp only [tree197,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox197 1 (1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) false,decode_split denominator ibox197 1 (1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_198 h,accepted_201 h⟩
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
private noncomputable def tree194 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree195 tree196
attribute [irreducible] tree194
private theorem accepted_194 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox194) tree194 = true := by
  simp only [tree194,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox194 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox194 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_195 h,accepted_196 h⟩
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
private noncomputable def tree191 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree192 tree193
attribute [irreducible] tree191
private theorem accepted_191 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox191) tree191 = true := by
  simp only [tree191,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox191 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox191 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_192 h,accepted_193 h⟩
private noncomputable def tree190 : TapeTree := .split 1 (((1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree191 tree194
attribute [irreducible] tree190
private theorem accepted_190 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox190) tree190 = true := by
  simp only [tree190,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox190 1 (1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) false,decode_split denominator ibox190 1 (1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_191 h,accepted_194 h⟩
private noncomputable def tree189 : TapeTree := .split 2 (((1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree190 tree197
attribute [irreducible] tree189
private theorem accepted_189 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox189) tree189 = true := by
  simp only [tree189,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox189 2 (1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 : Int) false,decode_split denominator ibox189 2 (1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_190 h,accepted_197 h⟩
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
private noncomputable def tree186 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree187 tree188
attribute [irreducible] tree186
private theorem accepted_186 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox186) tree186 = true := by
  simp only [tree186,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox186 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox186 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_187 h,accepted_188 h⟩
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
private noncomputable def tree183 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree184 tree185
attribute [irreducible] tree183
private theorem accepted_183 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox183) tree183 = true := by
  simp only [tree183,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox183 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox183 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_184 h,accepted_185 h⟩
private noncomputable def tree182 : TapeTree := .split 2 (((1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree183 tree186
attribute [irreducible] tree182
private theorem accepted_182 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox182) tree182 = true := by
  simp only [tree182,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox182 2 (1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 : Int) false,decode_split denominator ibox182 2 (1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_183 h,accepted_186 h⟩
private noncomputable def tree181 : TapeTree := .split 1 (((1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree182 tree189
attribute [irreducible] tree181
private theorem accepted_181 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox181) tree181 = true := by
  simp only [tree181,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox181 1 (1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 : Int) false,decode_split denominator ibox181 1 (1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_182 h,accepted_189 h⟩
private noncomputable def tree180 : TapeTree := .centered (candidateRows ibox180) (candidateRows (FixedTape.midBox ibox180))
attribute [irreducible] tree180
private theorem sign_180 : 2*denominator*(computed denominator (FixedTape.midBox ibox180)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox180).gradient k).lo.natAbs ((computed denominator ibox180).gradient k).hi.natAbs : Int)*((ibox180 k).hi-(ibox180 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox180
    (computed denominator ibox180) (computed denominator (FixedTape.midBox ibox180))
    (by decide +kernel)
private theorem midpoint_even_180 : ∀ k, 2 ∣ (ibox180 k).lo+(ibox180 k).hi := by decide +kernel
private theorem accepted_180 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox180) tree180 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox180 midpoint_even_180
  simp only [tree180,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox180,candidate_valid h (FixedTape.midBox ibox180),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox180 113 (FixedTape.rowsAux denominator ibox180 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox180) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_180
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
private noncomputable def tree178 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree179 tree180
attribute [irreducible] tree178
private theorem accepted_178 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox178) tree178 = true := by
  simp only [tree178,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox178 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox178 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_179 h,accepted_180 h⟩
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
private noncomputable def tree175 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree176 tree177
attribute [irreducible] tree175
private theorem accepted_175 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox175) tree175 = true := by
  simp only [tree175,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox175 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox175 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_176 h,accepted_177 h⟩
private noncomputable def tree174 : TapeTree := .split 1 (((1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree175 tree178
attribute [irreducible] tree174
private theorem accepted_174 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox174) tree174 = true := by
  simp only [tree174,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox174 1 (1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) false,decode_split denominator ibox174 1 (1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) true]
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
private noncomputable def tree171 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree172 tree173
attribute [irreducible] tree171
private theorem accepted_171 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox171) tree171 = true := by
  simp only [tree171,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox171 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox171 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
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
private noncomputable def tree168 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree169 tree170
attribute [irreducible] tree168
private theorem accepted_168 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox168) tree168 = true := by
  simp only [tree168,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox168 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox168 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_169 h,accepted_170 h⟩
private noncomputable def tree167 : TapeTree := .split 1 (((1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree168 tree171
attribute [irreducible] tree167
private theorem accepted_167 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox167) tree167 = true := by
  simp only [tree167,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox167 1 (1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) false,decode_split denominator ibox167 1 (1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_168 h,accepted_171 h⟩
private noncomputable def tree166 : TapeTree := .split 2 (((1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree167 tree174
attribute [irreducible] tree166
private theorem accepted_166 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox166) tree166 = true := by
  simp only [tree166,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox166 2 (1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) false,decode_split denominator ibox166 2 (1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_167 h,accepted_174 h⟩
private noncomputable def tree165 : TapeTree := .centered (candidateRows ibox165) (candidateRows (FixedTape.midBox ibox165))
attribute [irreducible] tree165
private theorem sign_165 : 2*denominator*(computed denominator (FixedTape.midBox ibox165)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox165).gradient k).lo.natAbs ((computed denominator ibox165).gradient k).hi.natAbs : Int)*((ibox165 k).hi-(ibox165 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox165
    (computed denominator ibox165) (computed denominator (FixedTape.midBox ibox165))
    (by decide +kernel)
private theorem midpoint_even_165 : ∀ k, 2 ∣ (ibox165 k).lo+(ibox165 k).hi := by decide +kernel
private theorem accepted_165 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox165) tree165 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox165 midpoint_even_165
  simp only [tree165,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox165,candidate_valid h (FixedTape.midBox ibox165),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox165 113 (FixedTape.rowsAux denominator ibox165 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox165) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_165
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
private noncomputable def tree163 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree164 tree165
attribute [irreducible] tree163
private theorem accepted_163 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox163) tree163 = true := by
  simp only [tree163,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox163 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox163 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_164 h,accepted_165 h⟩
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
private noncomputable def tree160 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree161 tree162
attribute [irreducible] tree160
private theorem accepted_160 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox160) tree160 = true := by
  simp only [tree160,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox160 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox160 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_161 h,accepted_162 h⟩
private noncomputable def tree159 : TapeTree := .split 2 (((1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree160 tree163
attribute [irreducible] tree159
private theorem accepted_159 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox159) tree159 = true := by
  simp only [tree159,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox159 2 (1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) false,decode_split denominator ibox159 2 (1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_160 h,accepted_163 h⟩
private noncomputable def tree158 : TapeTree := .split 1 (((1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree159 tree166
attribute [irreducible] tree158
private theorem accepted_158 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox158) tree158 = true := by
  simp only [tree158,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox158 1 (1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 : Int) false,decode_split denominator ibox158 1 (1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_159 h,accepted_166 h⟩
private noncomputable def tree157 : TapeTree := .split 2 (((1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree158 tree181
attribute [irreducible] tree157
private theorem accepted_157 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox157) tree157 = true := by
  simp only [tree157,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox157 2 (1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 : Int) false,decode_split denominator ibox157 2 (1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_158 h,accepted_181 h⟩
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
private noncomputable def tree154 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree155 tree156
attribute [irreducible] tree154
private theorem accepted_154 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox154) tree154 = true := by
  simp only [tree154,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox154 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox154 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_155 h,accepted_156 h⟩
private noncomputable def tree153 : TapeTree := .centered (candidateRows ibox153) (candidateRows (FixedTape.midBox ibox153))
attribute [irreducible] tree153
private theorem sign_153 : 2*denominator*(computed denominator (FixedTape.midBox ibox153)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox153).gradient k).lo.natAbs ((computed denominator ibox153).gradient k).hi.natAbs : Int)*((ibox153 k).hi-(ibox153 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox153
    (computed denominator ibox153) (computed denominator (FixedTape.midBox ibox153))
    (by decide +kernel)
private theorem midpoint_even_153 : ∀ k, 2 ∣ (ibox153 k).lo+(ibox153 k).hi := by decide +kernel
private theorem accepted_153 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox153) tree153 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox153 midpoint_even_153
  simp only [tree153,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox153,candidate_valid h (FixedTape.midBox ibox153),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox153 113 (FixedTape.rowsAux denominator ibox153 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox153) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_153
private noncomputable def tree152 : TapeTree := .split 1 (((1470881094183761602328956713986603684788676133868253733237278979410770959197413402409496294799119561289190532238540800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree153 tree154
attribute [irreducible] tree152
private theorem accepted_152 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox152) tree152 = true := by
  simp only [tree152,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox152 1 (1470881094183761602328956713986603684788676133868253733237278979410770959197413402409496294799119561289190532238540800000000000000000000000 : Int) false,decode_split denominator ibox152 1 (1470881094183761602328956713986603684788676133868253733237278979410770959197413402409496294799119561289190532238540800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_153 h,accepted_154 h⟩
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
private noncomputable def tree149 : TapeTree := .split 1 (((1470881094183761602328956713986603684788676133868253733237278979410770959197413402409496294799119561289190532238540800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree150 tree151
attribute [irreducible] tree149
private theorem accepted_149 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox149) tree149 = true := by
  simp only [tree149,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox149 1 (1470881094183761602328956713986603684788676133868253733237278979410770959197413402409496294799119561289190532238540800000000000000000000000 : Int) false,decode_split denominator ibox149 1 (1470881094183761602328956713986603684788676133868253733237278979410770959197413402409496294799119561289190532238540800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_150 h,accepted_151 h⟩
private noncomputable def tree148 : TapeTree := .split 2 (((1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree149 tree152
attribute [irreducible] tree148
private theorem accepted_148 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox148) tree148 = true := by
  simp only [tree148,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox148 2 (1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 : Int) false,decode_split denominator ibox148 2 (1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_149 h,accepted_152 h⟩
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
private noncomputable def tree145 : TapeTree := .split 1 (((1470881094183761602328956713986603684788676133868253733237278979410770959197413402409496294799119561289190532238540800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree146 tree147
attribute [irreducible] tree145
private theorem accepted_145 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox145) tree145 = true := by
  simp only [tree145,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox145 1 (1470881094183761602328956713986603684788676133868253733237278979410770959197413402409496294799119561289190532238540800000000000000000000000 : Int) false,decode_split denominator ibox145 1 (1470881094183761602328956713986603684788676133868253733237278979410770959197413402409496294799119561289190532238540800000000000000000000000 : Int) true]
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
private noncomputable def tree142 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree143 tree144
attribute [irreducible] tree142
private theorem accepted_142 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox142) tree142 = true := by
  simp only [tree142,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox142 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox142 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_143 h,accepted_144 h⟩
private noncomputable def tree141 : TapeTree := .split 2 (((1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree142 tree145
attribute [irreducible] tree141
private theorem accepted_141 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox141) tree141 = true := by
  simp only [tree141,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox141 2 (1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) false,decode_split denominator ibox141 2 (1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_142 h,accepted_145 h⟩
private noncomputable def tree140 : TapeTree := .split 2 (((1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree141 tree148
attribute [irreducible] tree140
private theorem accepted_140 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox140) tree140 = true := by
  simp only [tree140,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox140 2 (1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 : Int) false,decode_split denominator ibox140 2 (1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_141 h,accepted_148 h⟩
private noncomputable def tree139 : TapeTree := .split 1 (((1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree140 tree157
attribute [irreducible] tree139
private theorem accepted_139 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox139) tree139 = true := by
  simp only [tree139,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox139 1 (1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 : Int) false,decode_split denominator ibox139 1 (1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_140 h,accepted_157 h⟩
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
private noncomputable def tree136 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree137 tree138
attribute [irreducible] tree136
private theorem accepted_136 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox136) tree136 = true := by
  simp only [tree136,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox136 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox136 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_137 h,accepted_138 h⟩
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
private noncomputable def tree133 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree134 tree135
attribute [irreducible] tree133
private theorem accepted_133 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox133) tree133 = true := by
  simp only [tree133,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox133 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox133 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_134 h,accepted_135 h⟩
private noncomputable def tree132 : TapeTree := .split 1 (((1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree133 tree136
attribute [irreducible] tree132
private theorem accepted_132 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox132) tree132 = true := by
  simp only [tree132,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox132 1 (1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) false,decode_split denominator ibox132 1 (1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_133 h,accepted_136 h⟩
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
private noncomputable def tree129 : TapeTree := .split 1 (((1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree130 tree131
attribute [irreducible] tree129
private theorem accepted_129 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox129) tree129 = true := by
  simp only [tree129,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox129 1 (1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 : Int) false,decode_split denominator ibox129 1 (1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 : Int) true]
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
private noncomputable def tree126 : TapeTree := .split 2 (((565723497762985231664983351533309109534106205333943743552799607465681138152851308619037036461199831265073281630208000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree127 tree128
attribute [irreducible] tree126
private theorem accepted_126 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox126) tree126 = true := by
  simp only [tree126,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox126 2 (565723497762985231664983351533309109534106205333943743552799607465681138152851308619037036461199831265073281630208000000000000000000000000 : Int) false,decode_split denominator ibox126 2 (565723497762985231664983351533309109534106205333943743552799607465681138152851308619037036461199831265073281630208000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_127 h,accepted_128 h⟩
private noncomputable def tree125 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree126 tree129
attribute [irreducible] tree125
private theorem accepted_125 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox125) tree125 = true := by
  simp only [tree125,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox125 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox125 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
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
private noncomputable def tree122 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree123 tree124
attribute [irreducible] tree122
private theorem accepted_122 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox122) tree122 = true := by
  simp only [tree122,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox122 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox122 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_123 h,accepted_124 h⟩
private noncomputable def tree121 : TapeTree := .split 1 (((1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree122 tree125
attribute [irreducible] tree121
private theorem accepted_121 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox121) tree121 = true := by
  simp only [tree121,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox121 1 (1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) false,decode_split denominator ibox121 1 (1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_122 h,accepted_125 h⟩
private noncomputable def tree120 : TapeTree := .split 2 (((678868197315582277997980021839970931440927446400732492263359528958817365783421570342844443753439797518087937956249600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree121 tree132
attribute [irreducible] tree120
private theorem accepted_120 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox120) tree120 = true := by
  simp only [tree120,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox120 2 (678868197315582277997980021839970931440927446400732492263359528958817365783421570342844443753439797518087937956249600000000000000000000000 : Int) false,decode_split denominator ibox120 2 (678868197315582277997980021839970931440927446400732492263359528958817365783421570342844443753439797518087937956249600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_121 h,accepted_132 h⟩
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
private noncomputable def tree117 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree118 tree119
attribute [irreducible] tree117
private theorem accepted_117 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox117) tree117 = true := by
  simp only [tree117,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox117 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox117 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
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
private noncomputable def tree114 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree115 tree116
attribute [irreducible] tree114
private theorem accepted_114 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox114) tree114 = true := by
  simp only [tree114,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox114 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox114 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_115 h,accepted_116 h⟩
private noncomputable def tree113 : TapeTree := .split 2 (((678868197315582277997980021839970931440927446400732492263359528958817365783421570342844443753439797518087937956249600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree114 tree117
attribute [irreducible] tree113
private theorem accepted_113 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox113) tree113 = true := by
  simp only [tree113,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox113 2 (678868197315582277997980021839970931440927446400732492263359528958817365783421570342844443753439797518087937956249600000000000000000000000 : Int) false,decode_split denominator ibox113 2 (678868197315582277997980021839970931440927446400732492263359528958817365783421570342844443753439797518087937956249600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_114 h,accepted_117 h⟩
private noncomputable def tree112 : TapeTree := .split 1 (((1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree113 tree120
attribute [irreducible] tree112
private theorem accepted_112 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox112) tree112 = true := by
  simp only [tree112,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox112 1 (1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 : Int) false,decode_split denominator ibox112 1 (1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_113 h,accepted_120 h⟩
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
private noncomputable def tree109 : TapeTree := .split 2 (((339434098657791138998990010919985465720463723200366246131679764479408682891710785171422221876719898759043968978124800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree110 tree111
attribute [irreducible] tree109
private theorem accepted_109 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox109) tree109 = true := by
  simp only [tree109,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox109 2 (339434098657791138998990010919985465720463723200366246131679764479408682891710785171422221876719898759043968978124800000000000000000000000 : Int) false,decode_split denominator ibox109 2 (339434098657791138998990010919985465720463723200366246131679764479408682891710785171422221876719898759043968978124800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_110 h,accepted_111 h⟩
private noncomputable def tree108 : TapeTree := .centered (candidateRows ibox108) (candidateRows (FixedTape.midBox ibox108))
attribute [irreducible] tree108
private theorem sign_108 : 2*denominator*(computed denominator (FixedTape.midBox ibox108)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox108).gradient k).lo.natAbs ((computed denominator ibox108).gradient k).hi.natAbs : Int)*((ibox108 k).hi-(ibox108 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox108
    (computed denominator ibox108) (computed denominator (FixedTape.midBox ibox108))
    (by decide +kernel)
private theorem midpoint_even_108 : ∀ k, 2 ∣ (ibox108 k).lo+(ibox108 k).hi := by decide +kernel
private theorem accepted_108 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox108) tree108 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox108 midpoint_even_108
  simp only [tree108,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox108,candidate_valid h (FixedTape.midBox ibox108),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox108 113 (FixedTape.rowsAux denominator ibox108 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox108) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_108
private noncomputable def tree107 : TapeTree := .split 1 (((1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree108 tree109
attribute [irreducible] tree107
private theorem accepted_107 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox107) tree107 = true := by
  simp only [tree107,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox107 1 (1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 : Int) false,decode_split denominator ibox107 1 (1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_108 h,accepted_109 h⟩
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
private noncomputable def tree103 : TapeTree := .split 0 (((1730086002940564764558711609954193640391458931462228465959519682077332197098116204136482063071826747178287687998916732529424979722240000000 : Int) : ℚ)/(denominator : ℚ)) tree104 tree105
attribute [irreducible] tree103
private theorem accepted_103 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox103) tree103 = true := by
  simp only [tree103,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox103 0 (1730086002940564764558711609954193640391458931462228465959519682077332197098116204136482063071826747178287687998916732529424979722240000000 : Int) false,decode_split denominator ibox103 0 (1730086002940564764558711609954193640391458931462228465959519682077332197098116204136482063071826747178287687998916732529424979722240000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_104 h,accepted_105 h⟩
private noncomputable def tree102 : TapeTree := .split 2 (((113144699552597046332996670306661821906821241066788748710559921493136227630570261723807407292239966253014656326041600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree103 tree106
attribute [irreducible] tree102
private theorem accepted_102 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox102) tree102 = true := by
  simp only [tree102,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox102 2 (113144699552597046332996670306661821906821241066788748710559921493136227630570261723807407292239966253014656326041600000000000000000000000 : Int) false,decode_split denominator ibox102 2 (113144699552597046332996670306661821906821241066788748710559921493136227630570261723807407292239966253014656326041600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_103 h,accepted_106 h⟩
private noncomputable def tree101 : TapeTree := .face 1 true (candidateRows ibox101) tree102
attribute [irreducible] tree101
private theorem sign_101 : 0 ≤ ((computed denominator ibox101).gradient 1).lo := by decide +kernel
private theorem accepted_101 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox101) tree101 = true := by
  simp only [tree101,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox101,?_,accepted_102 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox101)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox101).gradient 1).lo) denominator_positive).2 sign_101
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
private noncomputable def tree98 : TapeTree := .split 1 (((1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree99 tree101
attribute [irreducible] tree98
private theorem accepted_98 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox98) tree98 = true := by
  simp only [tree98,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox98 1 (1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 : Int) false,decode_split denominator ibox98 1 (1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_99 h,accepted_101 h⟩
private noncomputable def tree97 : TapeTree := .split 2 (((226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree98 tree107
attribute [irreducible] tree97
private theorem accepted_97 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox97) tree97 = true := by
  simp only [tree97,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox97 2 (226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 : Int) false,decode_split denominator ibox97 2 (226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_98 h,accepted_107 h⟩
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
private noncomputable def tree94 : TapeTree := .split 2 (((226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree95 tree96
attribute [irreducible] tree94
private theorem accepted_94 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox94) tree94 = true := by
  simp only [tree94,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox94 2 (226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 : Int) false,decode_split denominator ibox94 2 (226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_95 h,accepted_96 h⟩
private noncomputable def tree93 : TapeTree := .split 1 (((1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree94 tree97
attribute [irreducible] tree93
private theorem accepted_93 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox93) tree93 = true := by
  simp only [tree93,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox93 1 (1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) false,decode_split denominator ibox93 1 (1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_94 h,accepted_97 h⟩
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
private noncomputable def tree90 : TapeTree := .split 2 (((339434098657791138998990010919985465720463723200366246131679764479408682891710785171422221876719898759043968978124800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree91 tree92
attribute [irreducible] tree90
private theorem accepted_90 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox90) tree90 = true := by
  simp only [tree90,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox90 2 (339434098657791138998990010919985465720463723200366246131679764479408682891710785171422221876719898759043968978124800000000000000000000000 : Int) false,decode_split denominator ibox90 2 (339434098657791138998990010919985465720463723200366246131679764479408682891710785171422221876719898759043968978124800000000000000000000000 : Int) true]
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
private noncomputable def tree88 : TapeTree := .split 1 (((1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree89 tree90
attribute [irreducible] tree88
private theorem accepted_88 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox88) tree88 = true := by
  simp only [tree88,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox88 1 (1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 : Int) false,decode_split denominator ibox88 1 (1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_89 h,accepted_90 h⟩
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
private noncomputable def tree84 : TapeTree := .split 0 (((1720713963123113865094750521238634464835157752092089036320396563851044617565860541467118157462182459799087791036750197588274939166720000000 : Int) : ℚ)/(denominator : ℚ)) tree85 tree86
attribute [irreducible] tree84
private theorem accepted_84 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox84) tree84 = true := by
  simp only [tree84,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox84 0 (1720713963123113865094750521238634464835157752092089036320396563851044617565860541467118157462182459799087791036750197588274939166720000000 : Int) false,decode_split denominator ibox84 0 (1720713963123113865094750521238634464835157752092089036320396563851044617565860541467118157462182459799087791036750197588274939166720000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_85 h,accepted_86 h⟩
private noncomputable def tree83 : TapeTree := .split 2 (((113144699552597046332996670306661821906821241066788748710559921493136227630570261723807407292239966253014656326041600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree84 tree87
attribute [irreducible] tree83
private theorem accepted_83 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox83) tree83 = true := by
  simp only [tree83,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox83 2 (113144699552597046332996670306661821906821241066788748710559921493136227630570261723807407292239966253014656326041600000000000000000000000 : Int) false,decode_split denominator ibox83 2 (113144699552597046332996670306661821906821241066788748710559921493136227630570261723807407292239966253014656326041600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_84 h,accepted_87 h⟩
private noncomputable def tree82 : TapeTree := .face 1 true (candidateRows ibox82) tree83
attribute [irreducible] tree82
private theorem sign_82 : 0 ≤ ((computed denominator ibox82).gradient 1).lo := by decide +kernel
private theorem accepted_82 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox82) tree82 = true := by
  simp only [tree82,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox82,?_,accepted_83 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox82)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox82).gradient 1).lo) denominator_positive).2 sign_82
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
private noncomputable def tree80 : TapeTree := .face 1 true (candidateRows ibox80) tree81
attribute [irreducible] tree80
private theorem sign_80 : 0 ≤ ((computed denominator ibox80).gradient 1).lo := by decide +kernel
private theorem accepted_80 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox80) tree80 = true := by
  simp only [tree80,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox80,?_,accepted_81 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox80)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox80).gradient 1).lo) denominator_positive).2 sign_80
private noncomputable def tree79 : TapeTree := .split 1 (((1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree80 tree82
attribute [irreducible] tree79
private theorem accepted_79 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox79) tree79 = true := by
  simp only [tree79,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox79 1 (1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 : Int) false,decode_split denominator ibox79 1 (1782029017953403479744697557329923695032434546801922792191318763516895585181481622149966664852779468484980837135155200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_80 h,accepted_82 h⟩
private noncomputable def tree78 : TapeTree := .split 2 (((226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree79 tree88
attribute [irreducible] tree78
private theorem accepted_78 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox78) tree78 = true := by
  simp only [tree78,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox78 2 (226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 : Int) false,decode_split denominator ibox78 2 (226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_79 h,accepted_88 h⟩
private noncomputable def tree77 : TapeTree := .centered (candidateRows ibox77) (candidateRows (FixedTape.midBox ibox77))
attribute [irreducible] tree77
private theorem sign_77 : 2*denominator*(computed denominator (FixedTape.midBox ibox77)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox77).gradient k).lo.natAbs ((computed denominator ibox77).gradient k).hi.natAbs : Int)*((ibox77 k).hi-(ibox77 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox77
    (computed denominator ibox77) (computed denominator (FixedTape.midBox ibox77))
    (by decide +kernel)
private theorem midpoint_even_77 : ∀ k, 2 ∣ (ibox77 k).lo+(ibox77 k).hi := by decide +kernel
private theorem accepted_77 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox77) tree77 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox77 midpoint_even_77
  simp only [tree77,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox77,candidate_valid h (FixedTape.midBox ibox77),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox77 113 (FixedTape.rowsAux denominator ibox77 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox77) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_77
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
private noncomputable def tree75 : TapeTree := .split 2 (((226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree76 tree77
attribute [irreducible] tree75
private theorem accepted_75 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox75) tree75 = true := by
  simp only [tree75,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox75 2 (226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 : Int) false,decode_split denominator ibox75 2 (226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_76 h,accepted_77 h⟩
private noncomputable def tree74 : TapeTree := .split 1 (((1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree75 tree78
attribute [irreducible] tree74
private theorem accepted_74 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox74) tree74 = true := by
  simp only [tree74,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox74 1 (1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) false,decode_split denominator ibox74 1 (1753742843065254218161448389753258239555729236535225605013678783143611528273839056719014813029719476921727173053644800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_75 h,accepted_78 h⟩
private noncomputable def tree73 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree74 tree93
attribute [irreducible] tree73
private theorem accepted_73 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox73) tree73 = true := by
  simp only [tree73,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox73 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox73 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_74 h,accepted_93 h⟩
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
private noncomputable def tree70 : TapeTree := .split 1 (((1640598143512657171828451719446596417648907995468436856303118861650475300643268794995207405737479510668712516727603200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree71 tree72
attribute [irreducible] tree70
private theorem accepted_70 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox70) tree70 = true := by
  simp only [tree70,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox70 1 (1640598143512657171828451719446596417648907995468436856303118861650475300643268794995207405737479510668712516727603200000000000000000000000 : Int) false,decode_split denominator ibox70 1 (1640598143512657171828451719446596417648907995468436856303118861650475300643268794995207405737479510668712516727603200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_71 h,accepted_72 h⟩
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
private noncomputable def tree67 : TapeTree := .split 2 (((226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree68 tree69
attribute [irreducible] tree67
private theorem accepted_67 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox67) tree67 = true := by
  simp only [tree67,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox67 2 (226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 : Int) false,decode_split denominator ibox67 2 (226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_68 h,accepted_69 h⟩
private noncomputable def tree66 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree67 tree70
attribute [irreducible] tree66
private theorem accepted_66 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox66) tree66 = true := by
  simp only [tree66,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox66 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox66 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_67 h,accepted_70 h⟩
private noncomputable def tree65 : TapeTree := .split 1 (((1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree66 tree73
attribute [irreducible] tree65
private theorem accepted_65 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox65) tree65 = true := by
  simp only [tree65,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox65 1 (1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 : Int) false,decode_split denominator ibox65 1 (1697170493288955694994950054599927328602318616001831230658398822397043414458553925857111109383599493795219844890624000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_66 h,accepted_73 h⟩
private noncomputable def tree64 : TapeTree := .split 2 (((452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree65 tree112
attribute [irreducible] tree64
private theorem accepted_64 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox64) tree64 = true := by
  simp only [tree64,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox64 2 (452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) false,decode_split denominator ibox64 2 (452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_65 h,accepted_112 h⟩
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
private noncomputable def tree61 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree62 tree63
attribute [irreducible] tree61
private theorem accepted_61 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox61) tree61 = true := by
  simp only [tree61,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox61 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox61 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_62 h,accepted_63 h⟩
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
private noncomputable def tree58 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree59 tree60
attribute [irreducible] tree58
private theorem accepted_58 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox58) tree58 = true := by
  simp only [tree58,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox58 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox58 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_59 h,accepted_60 h⟩
private noncomputable def tree57 : TapeTree := .split 2 (((452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree58 tree61
attribute [irreducible] tree57
private theorem accepted_57 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox57) tree57 = true := by
  simp only [tree57,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox57 2 (452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) false,decode_split denominator ibox57 2 (452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_58 h,accepted_61 h⟩
private noncomputable def tree56 : TapeTree := .split 1 (((1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree57 tree64
attribute [irreducible] tree56
private theorem accepted_56 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox56) tree56 = true := by
  simp only [tree56,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox56 1 (1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 : Int) false,decode_split denominator ibox56 1 (1584025793736358648661953384293265506695497374935042481947838900903907186827983664133303702091359527542205188564582400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_57 h,accepted_64 h⟩
private noncomputable def tree55 : TapeTree := .split 2 (((905157596420776370663973362453294575254569928534309989684479371945089821044562093790459258337919730024117250608332800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree56 tree139
attribute [irreducible] tree55
private theorem accepted_55 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox55) tree55 = true := by
  simp only [tree55,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox55 2 (905157596420776370663973362453294575254569928534309989684479371945089821044562093790459258337919730024117250608332800000000000000000000000 : Int) false,decode_split denominator ibox55 2 (905157596420776370663973362453294575254569928534309989684479371945089821044562093790459258337919730024117250608332800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_56 h,accepted_139 h⟩
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
private noncomputable def tree52 : TapeTree := .split 1 (((1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree53 tree54
attribute [irreducible] tree52
private theorem accepted_52 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox52) tree52 = true := by
  simp only [tree52,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox52 1 (1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) false,decode_split denominator ibox52 1 (1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_53 h,accepted_54 h⟩
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
private noncomputable def tree49 : TapeTree := .split 1 (((1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree50 tree51
attribute [irreducible] tree49
private theorem accepted_49 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox49) tree49 = true := by
  simp only [tree49,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox49 1 (1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) false,decode_split denominator ibox49 1 (1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_50 h,accepted_51 h⟩
private noncomputable def tree48 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree49 tree52
attribute [irreducible] tree48
private theorem accepted_48 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox48) tree48 = true := by
  simp only [tree48,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox48 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox48 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_49 h,accepted_52 h⟩
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
private noncomputable def tree45 : TapeTree := .split 1 (((1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree46 tree47
attribute [irreducible] tree45
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox45 1 (1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) false,decode_split denominator ibox45 1 (1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_46 h,accepted_47 h⟩
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
private noncomputable def tree43 : TapeTree := .centered (candidateRows ibox43) (candidateRows (FixedTape.midBox ibox43))
attribute [irreducible] tree43
private theorem sign_43 : 2*denominator*(computed denominator (FixedTape.midBox ibox43)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox43).gradient k).lo.natAbs ((computed denominator ibox43).gradient k).hi.natAbs : Int)*((ibox43 k).hi-(ibox43 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox43
    (computed denominator ibox43) (computed denominator (FixedTape.midBox ibox43))
    (by decide +kernel)
private theorem midpoint_even_43 : ∀ k, 2 ∣ (ibox43 k).lo+(ibox43 k).hi := by decide +kernel
private theorem accepted_43 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox43) tree43 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox43 midpoint_even_43
  simp only [tree43,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox43,candidate_valid h (FixedTape.midBox ibox43),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox43 113 (FixedTape.rowsAux denominator ibox43 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox43) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_43
private noncomputable def tree42 : TapeTree := .split 1 (((1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree43 tree44
attribute [irreducible] tree42
private theorem accepted_42 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox42) tree42 = true := by
  simp only [tree42,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox42 1 (1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) false,decode_split denominator ibox42 1 (1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_43 h,accepted_44 h⟩
private noncomputable def tree41 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree42 tree45
attribute [irreducible] tree41
private theorem accepted_41 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox41) tree41 = true := by
  simp only [tree41,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox41 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox41 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_42 h,accepted_45 h⟩
private noncomputable def tree40 : TapeTree := .split 2 (((1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree41 tree48
attribute [irreducible] tree40
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox40 2 (1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 : Int) false,decode_split denominator ibox40 2 (1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_41 h,accepted_48 h⟩
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
private noncomputable def tree37 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree38 tree39
attribute [irreducible] tree37
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox37 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox37 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
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
private noncomputable def tree35 : TapeTree := .split 1 (((1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree36 tree37
attribute [irreducible] tree35
private theorem accepted_35 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox35) tree35 = true := by
  simp only [tree35,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox35 1 (1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) false,decode_split denominator ibox35 1 (1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) true]
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
private noncomputable def tree32 : TapeTree := .split 1 (((1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree33 tree34
attribute [irreducible] tree32
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox32 1 (1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) false,decode_split denominator ibox32 1 (1131446995525970463329966703066618219068212410667887487105599214931362276305702617238074072922399662530146563260416000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_33 h,accepted_34 h⟩
private noncomputable def tree31 : TapeTree := .split 2 (((452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree32 tree35
attribute [irreducible] tree31
private theorem accepted_31 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox31) tree31 = true := by
  simp only [tree31,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox31 2 (452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) false,decode_split denominator ibox31 2 (452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_32 h,accepted_35 h⟩
private noncomputable def tree30 : TapeTree := .split 2 (((905157596420776370663973362453294575254569928534309989684479371945089821044562093790459258337919730024117250608332800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree31 tree40
attribute [irreducible] tree30
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox30 2 (905157596420776370663973362453294575254569928534309989684479371945089821044562093790459258337919730024117250608332800000000000000000000000 : Int) false,decode_split denominator ibox30 2 (905157596420776370663973362453294575254569928534309989684479371945089821044562093790459258337919730024117250608332800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_31 h,accepted_40 h⟩
private noncomputable def tree29 : TapeTree := .split 1 (((1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree30 tree55
attribute [irreducible] tree29
private theorem accepted_29 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox29) tree29 = true := by
  simp only [tree29,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox29 1 (1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 : Int) false,decode_split denominator ibox29 1 (1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_30 h,accepted_55 h⟩
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
private noncomputable def tree26 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree27 tree28
attribute [irreducible] tree26
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox26 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox26 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_27 h,accepted_28 h⟩
private noncomputable def tree25 : TapeTree := .centered (candidateRows ibox25) (candidateRows (FixedTape.midBox ibox25))
attribute [irreducible] tree25
private theorem sign_25 : 2*denominator*(computed denominator (FixedTape.midBox ibox25)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox25).gradient k).lo.natAbs ((computed denominator ibox25).gradient k).hi.natAbs : Int)*((ibox25 k).hi-(ibox25 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox25
    (computed denominator ibox25) (computed denominator (FixedTape.midBox ibox25))
    (by decide +kernel)
private theorem midpoint_even_25 : ∀ k, 2 ∣ (ibox25 k).lo+(ibox25 k).hi := by decide +kernel
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox25 midpoint_even_25
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox25,candidate_valid h (FixedTape.midBox ibox25),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox25 113 (FixedTape.rowsAux denominator ibox25 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox25) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_25
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
private noncomputable def tree23 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree24 tree25
attribute [irreducible] tree23
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox23 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox23 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_24 h,accepted_25 h⟩
private noncomputable def tree22 : TapeTree := .split 2 (((1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree23 tree26
attribute [irreducible] tree22
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox22 2 (1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 : Int) false,decode_split denominator ibox22 2 (1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_23 h,accepted_26 h⟩
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
private noncomputable def tree19 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree21
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox19 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
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
private noncomputable def tree16 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree18
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox16 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_17 h,accepted_18 h⟩
private noncomputable def tree15 : TapeTree := .split 2 (((1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree16 tree19
attribute [irreducible] tree15
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox15 2 (1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 : Int) false,decode_split denominator ibox15 2 (1357736394631164555995960043679941862881854892801464984526719057917634731566843140685688887506879595036175875912499200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_16 h,accepted_19 h⟩
private noncomputable def tree14 : TapeTree := .split 1 (((452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree15 tree22
attribute [irreducible] tree14
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox14 1 (452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) false,decode_split denominator ibox14 1 (452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_15 h,accepted_22 h⟩
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
private noncomputable def tree11 : TapeTree := .split 1 (((678868197315582277997980021839970931440927446400732492263359528958817365783421570342844443753439797518087937956249600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree12 tree13
attribute [irreducible] tree11
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox11 1 (678868197315582277997980021839970931440927446400732492263359528958817365783421570342844443753439797518087937956249600000000000000000000000 : Int) false,decode_split denominator ibox11 1 (678868197315582277997980021839970931440927446400732492263359528958817365783421570342844443753439797518087937956249600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_12 h,accepted_13 h⟩
private noncomputable def tree10 : TapeTree := .centered (candidateRows ibox10) (candidateRows (FixedTape.midBox ibox10))
attribute [irreducible] tree10
private theorem sign_10 : 2*denominator*(computed denominator (FixedTape.midBox ibox10)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox10).gradient k).lo.natAbs ((computed denominator ibox10).gradient k).hi.natAbs : Int)*((ibox10 k).hi-(ibox10 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox10
    (computed denominator ibox10) (computed denominator (FixedTape.midBox ibox10))
    (by decide +kernel)
private theorem midpoint_even_10 : ∀ k, 2 ∣ (ibox10 k).lo+(ibox10 k).hi := by decide +kernel
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox10 midpoint_even_10
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox10,candidate_valid h (FixedTape.midBox ibox10),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox10 113 (FixedTape.rowsAux denominator ibox10 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox10) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_10
private noncomputable def tree9 : TapeTree := .centered (candidateRows ibox9) (candidateRows (FixedTape.midBox ibox9))
attribute [irreducible] tree9
private theorem sign_9 : 2*denominator*(computed denominator (FixedTape.midBox ibox9)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox9).gradient k).lo.natAbs ((computed denominator ibox9).gradient k).hi.natAbs : Int)*((ibox9 k).hi-(ibox9 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox9
    (computed denominator ibox9) (computed denominator (FixedTape.midBox ibox9))
    (by decide +kernel)
private theorem midpoint_even_9 : ∀ k, 2 ∣ (ibox9 k).lo+(ibox9 k).hi := by decide +kernel
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox9 midpoint_even_9
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox9,candidate_valid h (FixedTape.midBox ibox9),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox9 113 (FixedTape.rowsAux denominator ibox9 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox9) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_9
private noncomputable def tree8 : TapeTree := .split 2 (((452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree9 tree10
attribute [irreducible] tree8
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox8 2 (452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) false,decode_split denominator ibox8 2 (452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_9 h,accepted_10 h⟩
private noncomputable def tree7 : TapeTree := .split 0 (((1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) : ℚ)/(denominator : ℚ)) tree8 tree11
attribute [irreducible] tree7
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox7 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) false,decode_split denominator ibox7 0 (1725399983031839314826731065596414052613308341777158751139958122964188407331988372801800110267004603488687739517833465058849959444480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_8 h,accepted_11 h⟩
private noncomputable def tree6 : TapeTree := .centered (candidateRows ibox6) (candidateRows (FixedTape.midBox ibox6))
attribute [irreducible] tree6
private theorem sign_6 : 2*denominator*(computed denominator (FixedTape.midBox ibox6)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox6).gradient k).lo.natAbs ((computed denominator ibox6).gradient k).hi.natAbs : Int)*((ibox6 k).hi-(ibox6 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox6
    (computed denominator ibox6) (computed denominator (FixedTape.midBox ibox6))
    (by decide +kernel)
private theorem midpoint_even_6 : ∀ k, 2 ∣ (ibox6 k).lo+(ibox6 k).hi := by decide +kernel
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox6 midpoint_even_6
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox6,candidate_valid h (FixedTape.midBox ibox6),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox6 113 (FixedTape.rowsAux denominator ibox6 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox6) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_6
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
private noncomputable def tree4 : TapeTree := .split 2 (((452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree6
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 2 (452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) false,decode_split denominator ibox4 2 (452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_6 h⟩
private noncomputable def tree3 : TapeTree := .split 1 (((452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree7
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) false,decode_split denominator ibox3 1 (452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_7 h⟩
private noncomputable def tree2 : TapeTree := .split 2 (((905157596420776370663973362453294575254569928534309989684479371945089821044562093790459258337919730024117250608332800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree14
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 2 (905157596420776370663973362453294575254569928534309989684479371945089821044562093790459258337919730024117250608332800000000000000000000000 : Int) false,decode_split denominator ibox2 2 (905157596420776370663973362453294575254569928534309989684479371945089821044562093790459258337919730024117250608332800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_14 h⟩
private noncomputable def tree1 : TapeTree := .split 1 (((905157596420776370663973362453294575254569928534309989684479371945089821044562093790459258337919730024117250608332800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree2 tree29
attribute [irreducible] tree1
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 113 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox1 1 (905157596420776370663973362453294575254569928534309989684479371945089821044562093790459258337919730024117250608332800000000000000000000000 : Int) false,decode_split denominator ibox1 1 (905157596420776370663973362453294575254569928534309989684479371945089821044562093790459258337919730024117250608332800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_2 h,accepted_29 h⟩
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
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (4739583333333333/5000000000000000 : ℚ) (4395636133505499103505449720174017696700000/4587050499937430843922117419533744845930749 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 113 = e123 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (4739583333333333/5000000000000000 : ℚ) (4395636133505499103505449720174017696700000/4587050499937430843922117419533744845930749 : ℚ)) x → eval e123 x ≤ 0 := by
  have hb := h.child_4 tape 113 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell121_high_internal_top

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell121_high_internal_top
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((4739583333333333/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((4395636133505499103505449720174017696700000/4587050499937430843922117419533744845930749 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 121 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 121 p)
    (hkb : ((4395636133505499103505449720174017696700000/4587050499937430843922117419533744845930749 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((4739583333333333/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : bStar < a), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell121_high_internal_top.cell_bound h.child_8 h.child_9 (Cell121_high_internal_top.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell121_high_internal_top
