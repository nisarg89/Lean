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
namespace Cell51_low_internal
private noncomputable def qValues : Fin 4 → ℚ := ![(4001632192829017668449294638547797766/5475919222521178068566161688925867211 : ℚ),(88703359461463666811230000000000000000/60235111447732958754227778578184539321 : ℚ),(3766795493616465885132721994210715767/1585777177026860822837307395029303812 : ℚ),(-4083439388264298746867500000000000000/4360887236823867262802595336330585483 : ℚ)]
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
    priceLambda 51 p = ((4001632192829017668449294638547797766/5475919222521178068566161688925867211 : ℝ)+(88703359461463666811230000000000000000/60235111447732958754227778578184539321 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell51,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 51 p = (((3766795493616465885132721994210715767/1585777177026860822837307395029303812 : ℝ)+(-4083439388264298746867500000000000000/4360887236823867262802595336330585483 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell51,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e114 x = (x 0*(1-x 0))*(aPoint x+priceLambda 51 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 51 (x 0)*psiStar (rPoint x)+(0)-(0)) := by
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
    (hL : lambdaStar (x 0) = priceLambda 51 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 51 (x 0)) :
    (1)*eval e114 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,if_pos hA,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (3333333333333333/10000000000000000 : ℚ) (11/32 : ℚ)) x → eval e114 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((3333333333333333/10000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((11/32 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 51 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 51 p)
    (hk0 : ((11/32 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((3333333333333333/10000000000000000 : ℚ) : ℝ))
    (hk1 : ((11/32 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((3333333333333333/10000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h3 (3333333333333333/10000000000000000 : ℚ) (11/32 : ℚ) ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ) p a A r hpcell hk0 hk1 hr ha hap hpA hAr
  have hcut : ((11/32 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 51 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 51 (x 0) := by simpa only [hxp] using hT
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
.const (4001632192829017668449294638547797766/5475919222521178068566161688925867211 : ℚ),
.const (88703359461463666811230000000000000000/60235111447732958754227778578184539321 : ℚ),
.mul 74 1,
.add 73 75,
.const (3766795493616465885132721994210715767/1585777177026860822837307395029303812 : ℚ),
.const (-4083439388264298746867500000000000000/4360887236823867262802595336330585483 : ℚ),
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
private noncomputable def ssaQVals : Fin 16 → ℚ := ![(1/1 : ℚ),(49/100 : ℚ),(390189/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(4001632192829017668449294638547797766/5475919222521178068566161688925867211 : ℚ),(88703359461463666811230000000000000000/60235111447732958754227778578184539321 : ℚ),(3766795493616465885132721994210715767/1585777177026860822837307395029303812 : ℚ),(-4083439388264298746867500000000000000/4360887236823867262802595336330585483 : ℚ),(-145513/100000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
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
private noncomputable def denominator : Int := 5444477933396750644760738013968344295028065096724449013090707725600516001455553005591031552409600000000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨1814825977798916700104314891431093272984754566630006503428066017718538230794926815179810468951433146965614919680000000,1871539289605133034136503692301618351415897376999029348249930780675177375500346345671917096140800000000000000000000000⟩,⟨0,5444477933396750644760738013968344295028065096724449013090707725600516001455553005591031552409600000000000000000000000⟩,⟨0,5444477933396750644760738013968344295028065096724449013090707725600516001455553005591031552409600000000000000000000000⟩,⟨0,5444477933396750644760738013968344295028065096724449013090707725600516001455553005591031552409600000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := splitI ibox0 1 2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := splitI ibox1 2 2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := faceI ibox2 1 true
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox1 2 2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 true
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 2 4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := faceI ibox5 1 true
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox4 2 4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 true
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox7 1 1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 false
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox7 1 1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox9 2 4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 false
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox9 2 4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox0 1 2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 true
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox12 2 2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 false
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox13 1 4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 false
private noncomputable def ibox15 : Fin 4 → FixedTape.I := faceI ibox14 1 true
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox15 2 1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 false
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox15 2 1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 true
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox13 1 4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := faceI ibox18 1 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 2 1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox20 3 2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 false
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox20 3 2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 true
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox19 2 1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 true
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox23 3 2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 false
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox24 3 1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 false
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox24 3 1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 true
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox23 3 2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 true
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox12 2 2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 true
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox28 1 4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 false
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox29 2 4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 false
private noncomputable def ibox31 : Fin 4 → FixedTape.I := faceI ibox30 1 true
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox29 2 4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 true
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox32 2 4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 false
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox32 2 4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 true
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox34 1 3402798708372969152975461258730215184392540685452780633181692328500322500909720628494394720256000000000000000000000000 false
private noncomputable def ibox36 : Fin 4 → FixedTape.I := splitI ibox34 1 3402798708372969152975461258730215184392540685452780633181692328500322500909720628494394720256000000000000000000000000 true
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox28 1 4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 true
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox37 2 4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 false
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox38 3 2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 false
private noncomputable def ibox40 : Fin 4 → FixedTape.I := faceI ibox39 1 true
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox40 3 1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 false
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox40 3 1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 true
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox38 3 2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 true
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox43 1 4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 false
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox43 1 4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 true
private noncomputable def ibox46 : Fin 4 → FixedTape.I := faceI ibox45 1 true
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox37 2 4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 true
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox47 3 2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 false
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox48 1 4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 false
private noncomputable def ibox50 : Fin 4 → FixedTape.I := faceI ibox49 1 true
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox48 1 4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 true
private noncomputable def ibox52 : Fin 4 → FixedTape.I := faceI ibox51 1 true
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox52 3 1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 false
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox52 3 1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 true
private noncomputable def ibox55 : Fin 4 → FixedTape.I := splitI ibox47 3 2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 true
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox55 1 4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 false
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox56 2 4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 false
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox56 2 4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 true
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox55 1 4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 true
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox59 2 4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 false
private noncomputable def ibox61 : Fin 4 → FixedTape.I := splitI ibox59 2 4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 true
private noncomputable def tree61 : TapeTree := .centered (candidateRows ibox61) (candidateRows (FixedTape.midBox ibox61))
attribute [irreducible] tree61
private theorem sign_61 : 2*denominator*(computed denominator (FixedTape.midBox ibox61)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox61).gradient k).lo.natAbs ((computed denominator ibox61).gradient k).hi.natAbs : Int)*((ibox61 k).hi-(ibox61 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox61
    (computed denominator ibox61) (computed denominator (FixedTape.midBox ibox61))
    (by decide +kernel)
private theorem midpoint_even_61 : ∀ k, 2 ∣ (ibox61 k).lo+(ibox61 k).hi := by decide +kernel
private theorem accepted_61 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox61) tree61 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox61 midpoint_even_61
  simp only [tree61,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox61,candidate_valid h (FixedTape.midBox ibox61),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox61 106 (FixedTape.rowsAux denominator ibox61 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox61) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_61
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
private noncomputable def tree59 : TapeTree := .split 2 (((4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree60 tree61
attribute [irreducible] tree59
private theorem accepted_59 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox59) tree59 = true := by
  simp only [tree59,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox59 2 (4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) false,decode_split denominator ibox59 2 (4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_60 h,accepted_61 h⟩
private noncomputable def tree58 : TapeTree := .centered (candidateRows ibox58) (candidateRows (FixedTape.midBox ibox58))
attribute [irreducible] tree58
private theorem sign_58 : 2*denominator*(computed denominator (FixedTape.midBox ibox58)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox58).gradient k).lo.natAbs ((computed denominator ibox58).gradient k).hi.natAbs : Int)*((ibox58 k).hi-(ibox58 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox58
    (computed denominator ibox58) (computed denominator (FixedTape.midBox ibox58))
    (by decide +kernel)
private theorem midpoint_even_58 : ∀ k, 2 ∣ (ibox58 k).lo+(ibox58 k).hi := by decide +kernel
private theorem accepted_58 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox58) tree58 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox58 midpoint_even_58
  simp only [tree58,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox58,candidate_valid h (FixedTape.midBox ibox58),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox58 106 (FixedTape.rowsAux denominator ibox58 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox58) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_58
private noncomputable def tree57 : TapeTree := .centered (candidateRows ibox57) (candidateRows (FixedTape.midBox ibox57))
attribute [irreducible] tree57
private theorem sign_57 : 2*denominator*(computed denominator (FixedTape.midBox ibox57)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox57).gradient k).lo.natAbs ((computed denominator ibox57).gradient k).hi.natAbs : Int)*((ibox57 k).hi-(ibox57 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox57
    (computed denominator ibox57) (computed denominator (FixedTape.midBox ibox57))
    (by decide +kernel)
private theorem midpoint_even_57 : ∀ k, 2 ∣ (ibox57 k).lo+(ibox57 k).hi := by decide +kernel
private theorem accepted_57 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox57) tree57 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox57 midpoint_even_57
  simp only [tree57,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox57,candidate_valid h (FixedTape.midBox ibox57),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox57 106 (FixedTape.rowsAux denominator ibox57 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox57) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_57
private noncomputable def tree56 : TapeTree := .split 2 (((4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree57 tree58
attribute [irreducible] tree56
private theorem accepted_56 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox56) tree56 = true := by
  simp only [tree56,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox56 2 (4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) false,decode_split denominator ibox56 2 (4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_57 h,accepted_58 h⟩
private noncomputable def tree55 : TapeTree := .split 1 (((4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree56 tree59
attribute [irreducible] tree55
private theorem accepted_55 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox55) tree55 = true := by
  simp only [tree55,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox55 1 (4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) false,decode_split denominator ibox55 1 (4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_56 h,accepted_59 h⟩
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
private noncomputable def tree53 : TapeTree := .centered (candidateRows ibox53) (candidateRows (FixedTape.midBox ibox53))
attribute [irreducible] tree53
private theorem sign_53 : 2*denominator*(computed denominator (FixedTape.midBox ibox53)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox53).gradient k).lo.natAbs ((computed denominator ibox53).gradient k).hi.natAbs : Int)*((ibox53 k).hi-(ibox53 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox53
    (computed denominator ibox53) (computed denominator (FixedTape.midBox ibox53))
    (by decide +kernel)
private theorem midpoint_even_53 : ∀ k, 2 ∣ (ibox53 k).lo+(ibox53 k).hi := by decide +kernel
private theorem accepted_53 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox53) tree53 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox53 midpoint_even_53
  simp only [tree53,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox53,candidate_valid h (FixedTape.midBox ibox53),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox53 106 (FixedTape.rowsAux denominator ibox53 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox53) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_53
private noncomputable def tree52 : TapeTree := .split 3 (((1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree53 tree54
attribute [irreducible] tree52
private theorem accepted_52 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox52) tree52 = true := by
  simp only [tree52,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox52 3 (1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 : Int) false,decode_split denominator ibox52 3 (1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_53 h,accepted_54 h⟩
private noncomputable def tree51 : TapeTree := .face 1 true (candidateRows ibox51) tree52
attribute [irreducible] tree51
private theorem sign_51 : 0 ≤ ((computed denominator ibox51).gradient 1).lo := by decide +kernel
private theorem accepted_51 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox51) tree51 = true := by
  simp only [tree51,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox51,?_,accepted_52 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox51)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox51).gradient 1).lo) denominator_positive).2 sign_51
private noncomputable def tree50 : TapeTree := .centered (candidateRows ibox50) (candidateRows (FixedTape.midBox ibox50))
attribute [irreducible] tree50
private theorem sign_50 : 2*denominator*(computed denominator (FixedTape.midBox ibox50)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox50).gradient k).lo.natAbs ((computed denominator ibox50).gradient k).hi.natAbs : Int)*((ibox50 k).hi-(ibox50 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox50
    (computed denominator ibox50) (computed denominator (FixedTape.midBox ibox50))
    (by decide +kernel)
private theorem midpoint_even_50 : ∀ k, 2 ∣ (ibox50 k).lo+(ibox50 k).hi := by decide +kernel
private theorem accepted_50 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox50) tree50 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox50 midpoint_even_50
  simp only [tree50,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox50,candidate_valid h (FixedTape.midBox ibox50),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox50 106 (FixedTape.rowsAux denominator ibox50 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox50) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_50
private noncomputable def tree49 : TapeTree := .face 1 true (candidateRows ibox49) tree50
attribute [irreducible] tree49
private theorem sign_49 : 0 ≤ ((computed denominator ibox49).gradient 1).lo := by decide +kernel
private theorem accepted_49 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox49) tree49 = true := by
  simp only [tree49,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox49,?_,accepted_50 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox49)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox49).gradient 1).lo) denominator_positive).2 sign_49
private noncomputable def tree48 : TapeTree := .split 1 (((4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree49 tree51
attribute [irreducible] tree48
private theorem accepted_48 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox48) tree48 = true := by
  simp only [tree48,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox48 1 (4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) false,decode_split denominator ibox48 1 (4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_49 h,accepted_51 h⟩
private noncomputable def tree47 : TapeTree := .split 3 (((2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree48 tree55
attribute [irreducible] tree47
private theorem accepted_47 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox47) tree47 = true := by
  simp only [tree47,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox47 3 (2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) false,decode_split denominator ibox47 3 (2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_48 h,accepted_55 h⟩
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
private noncomputable def tree45 : TapeTree := .face 1 true (candidateRows ibox45) tree46
attribute [irreducible] tree45
private theorem sign_45 : 0 ≤ ((computed denominator ibox45).gradient 1).lo := by decide +kernel
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox45,?_,accepted_46 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox45)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox45).gradient 1).lo) denominator_positive).2 sign_45
private noncomputable def tree44 : TapeTree := .centered (candidateRows ibox44) (candidateRows (FixedTape.midBox ibox44))
attribute [irreducible] tree44
private theorem sign_44 : 2*denominator*(computed denominator (FixedTape.midBox ibox44)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox44).gradient k).lo.natAbs ((computed denominator ibox44).gradient k).hi.natAbs : Int)*((ibox44 k).hi-(ibox44 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox44
    (computed denominator ibox44) (computed denominator (FixedTape.midBox ibox44))
    (by decide +kernel)
private theorem midpoint_even_44 : ∀ k, 2 ∣ (ibox44 k).lo+(ibox44 k).hi := by decide +kernel
private theorem accepted_44 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox44) tree44 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox44 midpoint_even_44
  simp only [tree44,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox44,candidate_valid h (FixedTape.midBox ibox44),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox44 106 (FixedTape.rowsAux denominator ibox44 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox44) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_44
private noncomputable def tree43 : TapeTree := .split 1 (((4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree44 tree45
attribute [irreducible] tree43
private theorem accepted_43 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox43) tree43 = true := by
  simp only [tree43,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox43 1 (4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) false,decode_split denominator ibox43 1 (4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_44 h,accepted_45 h⟩
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
private noncomputable def tree40 : TapeTree := .split 3 (((1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree41 tree42
attribute [irreducible] tree40
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox40 3 (1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 : Int) false,decode_split denominator ibox40 3 (1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_41 h,accepted_42 h⟩
private noncomputable def tree39 : TapeTree := .face 1 true (candidateRows ibox39) tree40
attribute [irreducible] tree39
private theorem sign_39 : 0 ≤ ((computed denominator ibox39).gradient 1).lo := by decide +kernel
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox39,?_,accepted_40 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox39)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox39).gradient 1).lo) denominator_positive).2 sign_39
private noncomputable def tree38 : TapeTree := .split 3 (((2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree39 tree43
attribute [irreducible] tree38
private theorem accepted_38 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox38) tree38 = true := by
  simp only [tree38,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox38 3 (2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) false,decode_split denominator ibox38 3 (2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_39 h,accepted_43 h⟩
private noncomputable def tree37 : TapeTree := .split 2 (((4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree38 tree47
attribute [irreducible] tree37
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox37 2 (4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 : Int) false,decode_split denominator ibox37 2 (4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_38 h,accepted_47 h⟩
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
private noncomputable def tree34 : TapeTree := .split 1 (((3402798708372969152975461258730215184392540685452780633181692328500322500909720628494394720256000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree35 tree36
attribute [irreducible] tree34
private theorem accepted_34 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox34) tree34 = true := by
  simp only [tree34,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox34 1 (3402798708372969152975461258730215184392540685452780633181692328500322500909720628494394720256000000000000000000000000 : Int) false,decode_split denominator ibox34 1 (3402798708372969152975461258730215184392540685452780633181692328500322500909720628494394720256000000000000000000000000 : Int) true]
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
private noncomputable def tree32 : TapeTree := .split 2 (((4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree33 tree34
attribute [irreducible] tree32
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox32 2 (4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) false,decode_split denominator ibox32 2 (4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_33 h,accepted_34 h⟩
private noncomputable def tree31 : TapeTree := .centered (candidateRows ibox31) (candidateRows (FixedTape.midBox ibox31))
attribute [irreducible] tree31
private theorem sign_31 : 2*denominator*(computed denominator (FixedTape.midBox ibox31)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox31).gradient k).lo.natAbs ((computed denominator ibox31).gradient k).hi.natAbs : Int)*((ibox31 k).hi-(ibox31 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox31
    (computed denominator ibox31) (computed denominator (FixedTape.midBox ibox31))
    (by decide +kernel)
private theorem midpoint_even_31 : ∀ k, 2 ∣ (ibox31 k).lo+(ibox31 k).hi := by decide +kernel
private theorem accepted_31 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox31) tree31 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox31 midpoint_even_31
  simp only [tree31,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox31,candidate_valid h (FixedTape.midBox ibox31),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox31 106 (FixedTape.rowsAux denominator ibox31 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox31) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_31
private noncomputable def tree30 : TapeTree := .face 1 true (candidateRows ibox30) tree31
attribute [irreducible] tree30
private theorem sign_30 : 0 ≤ ((computed denominator ibox30).gradient 1).lo := by decide +kernel
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox30,?_,accepted_31 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox30)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox30).gradient 1).lo) denominator_positive).2 sign_30
private noncomputable def tree29 : TapeTree := .split 2 (((4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree30 tree32
attribute [irreducible] tree29
private theorem accepted_29 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox29) tree29 = true := by
  simp only [tree29,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox29 2 (4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 : Int) false,decode_split denominator ibox29 2 (4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_30 h,accepted_32 h⟩
private noncomputable def tree28 : TapeTree := .split 1 (((4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree29 tree37
attribute [irreducible] tree28
private theorem accepted_28 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox28) tree28 = true := by
  simp only [tree28,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox28 1 (4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 : Int) false,decode_split denominator ibox28 1 (4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_29 h,accepted_37 h⟩
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
private noncomputable def tree26 : TapeTree := .centered (candidateRows ibox26) (candidateRows (FixedTape.midBox ibox26))
attribute [irreducible] tree26
private theorem sign_26 : 2*denominator*(computed denominator (FixedTape.midBox ibox26)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox26).gradient k).lo.natAbs ((computed denominator ibox26).gradient k).hi.natAbs : Int)*((ibox26 k).hi-(ibox26 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox26
    (computed denominator ibox26) (computed denominator (FixedTape.midBox ibox26))
    (by decide +kernel)
private theorem midpoint_even_26 : ∀ k, 2 ∣ (ibox26 k).lo+(ibox26 k).hi := by decide +kernel
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox26 midpoint_even_26
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox26,candidate_valid h (FixedTape.midBox ibox26),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox26 106 (FixedTape.rowsAux denominator ibox26 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox26) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_26
private noncomputable def tree25 : TapeTree := .centered (candidateRows ibox25) (candidateRows (FixedTape.midBox ibox25))
attribute [irreducible] tree25
private theorem sign_25 : 2*denominator*(computed denominator (FixedTape.midBox ibox25)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox25).gradient k).lo.natAbs ((computed denominator ibox25).gradient k).hi.natAbs : Int)*((ibox25 k).hi-(ibox25 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox25
    (computed denominator ibox25) (computed denominator (FixedTape.midBox ibox25))
    (by decide +kernel)
private theorem midpoint_even_25 : ∀ k, 2 ∣ (ibox25 k).lo+(ibox25 k).hi := by decide +kernel
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox25 midpoint_even_25
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox25,candidate_valid h (FixedTape.midBox ibox25),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox25 106 (FixedTape.rowsAux denominator ibox25 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox25) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_25
private noncomputable def tree24 : TapeTree := .split 3 (((1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree25 tree26
attribute [irreducible] tree24
private theorem accepted_24 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox24) tree24 = true := by
  simp only [tree24,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox24 3 (1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 : Int) false,decode_split denominator ibox24 3 (1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_25 h,accepted_26 h⟩
private noncomputable def tree23 : TapeTree := .split 3 (((2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree24 tree27
attribute [irreducible] tree23
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox23 3 (2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) false,decode_split denominator ibox23 3 (2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_24 h,accepted_27 h⟩
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
private noncomputable def tree21 : TapeTree := .centered (candidateRows ibox21) (candidateRows (FixedTape.midBox ibox21))
attribute [irreducible] tree21
private theorem sign_21 : 2*denominator*(computed denominator (FixedTape.midBox ibox21)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox21).gradient k).lo.natAbs ((computed denominator ibox21).gradient k).hi.natAbs : Int)*((ibox21 k).hi-(ibox21 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox21
    (computed denominator ibox21) (computed denominator (FixedTape.midBox ibox21))
    (by decide +kernel)
private theorem midpoint_even_21 : ∀ k, 2 ∣ (ibox21 k).lo+(ibox21 k).hi := by decide +kernel
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox21 midpoint_even_21
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox21,candidate_valid h (FixedTape.midBox ibox21),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox21 106 (FixedTape.rowsAux denominator ibox21 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox21) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_21
private noncomputable def tree20 : TapeTree := .split 3 (((2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree21 tree22
attribute [irreducible] tree20
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox20 3 (2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) false,decode_split denominator ibox20 3 (2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_21 h,accepted_22 h⟩
private noncomputable def tree19 : TapeTree := .split 2 (((1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree23
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 2 (1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 : Int) false,decode_split denominator ibox19 2 (1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_20 h,accepted_23 h⟩
private noncomputable def tree18 : TapeTree := .face 1 true (candidateRows ibox18) tree19
attribute [irreducible] tree18
private theorem sign_18 : 0 ≤ ((computed denominator ibox18).gradient 1).lo := by decide +kernel
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox18,?_,accepted_19 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox18)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox18).gradient 1).lo) denominator_positive).2 sign_18
private noncomputable def tree17 : TapeTree := .centered (candidateRows ibox17) (candidateRows (FixedTape.midBox ibox17))
attribute [irreducible] tree17
private theorem sign_17 : 2*denominator*(computed denominator (FixedTape.midBox ibox17)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox17).gradient k).lo.natAbs ((computed denominator ibox17).gradient k).hi.natAbs : Int)*((ibox17 k).hi-(ibox17 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox17
    (computed denominator ibox17) (computed denominator (FixedTape.midBox ibox17))
    (by decide +kernel)
private theorem midpoint_even_17 : ∀ k, 2 ∣ (ibox17 k).lo+(ibox17 k).hi := by decide +kernel
private theorem accepted_17 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox17) tree17 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox17 midpoint_even_17
  simp only [tree17,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox17,candidate_valid h (FixedTape.midBox ibox17),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox17 106 (FixedTape.rowsAux denominator ibox17 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox17) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_17
private noncomputable def tree16 : TapeTree := .centered (candidateRows ibox16) (candidateRows (FixedTape.midBox ibox16))
attribute [irreducible] tree16
private theorem sign_16 : 2*denominator*(computed denominator (FixedTape.midBox ibox16)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox16).gradient k).lo.natAbs ((computed denominator ibox16).gradient k).hi.natAbs : Int)*((ibox16 k).hi-(ibox16 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox16
    (computed denominator ibox16) (computed denominator (FixedTape.midBox ibox16))
    (by decide +kernel)
private theorem midpoint_even_16 : ∀ k, 2 ∣ (ibox16 k).lo+(ibox16 k).hi := by decide +kernel
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox16 midpoint_even_16
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox16,candidate_valid h (FixedTape.midBox ibox16),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox16 106 (FixedTape.rowsAux denominator ibox16 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox16) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_16
private noncomputable def tree15 : TapeTree := .split 2 (((1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree16 tree17
attribute [irreducible] tree15
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox15 2 (1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 : Int) false,decode_split denominator ibox15 2 (1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_16 h,accepted_17 h⟩
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
private noncomputable def tree13 : TapeTree := .split 1 (((4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree14 tree18
attribute [irreducible] tree13
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox13 1 (4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 : Int) false,decode_split denominator ibox13 1 (4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_14 h,accepted_18 h⟩
private noncomputable def tree12 : TapeTree := .split 2 (((2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree13 tree28
attribute [irreducible] tree12
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox12 2 (2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) false,decode_split denominator ibox12 2 (2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_13 h,accepted_28 h⟩
private noncomputable def tree11 : TapeTree := .centered (candidateRows ibox11) (candidateRows (FixedTape.midBox ibox11))
attribute [irreducible] tree11
private theorem sign_11 : 2*denominator*(computed denominator (FixedTape.midBox ibox11)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox11).gradient k).lo.natAbs ((computed denominator ibox11).gradient k).hi.natAbs : Int)*((ibox11 k).hi-(ibox11 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox11
    (computed denominator ibox11) (computed denominator (FixedTape.midBox ibox11))
    (by decide +kernel)
private theorem midpoint_even_11 : ∀ k, 2 ∣ (ibox11 k).lo+(ibox11 k).hi := by decide +kernel
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox11 midpoint_even_11
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox11,candidate_valid h (FixedTape.midBox ibox11),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox11 106 (FixedTape.rowsAux denominator ibox11 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox11) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_11
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
private noncomputable def tree9 : TapeTree := .split 2 (((4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree10 tree11
attribute [irreducible] tree9
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox9 2 (4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) false,decode_split denominator ibox9 2 (4763918191722156814165645762222301258149556959633892886454369259900451501273608879892152608358400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_10 h,accepted_11 h⟩
private noncomputable def tree8 : TapeTree := .centered (candidateRows ibox8) (candidateRows (FixedTape.midBox ibox8))
attribute [irreducible] tree8
private theorem sign_8 : 2*denominator*(computed denominator (FixedTape.midBox ibox8)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox8).gradient k).lo.natAbs ((computed denominator ibox8).gradient k).hi.natAbs : Int)*((ibox8 k).hi-(ibox8 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox8
    (computed denominator ibox8) (computed denominator (FixedTape.midBox ibox8))
    (by decide +kernel)
private theorem midpoint_even_8 : ∀ k, 2 ∣ (ibox8 k).lo+(ibox8 k).hi := by decide +kernel
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox8 midpoint_even_8
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox8,candidate_valid h (FixedTape.midBox ibox8),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox8 106 (FixedTape.rowsAux denominator ibox8 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox8) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_8
private noncomputable def tree7 : TapeTree := .split 1 (((1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree8 tree9
attribute [irreducible] tree7
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox7 1 (1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 : Int) false,decode_split denominator ibox7 1 (1361119483349187661190184503492086073757016274181112253272676931400129000363888251397757888102400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_8 h,accepted_9 h⟩
private noncomputable def tree6 : TapeTree := .centered (candidateRows ibox6) (candidateRows (FixedTape.midBox ibox6))
attribute [irreducible] tree6
private theorem sign_6 : 2*denominator*(computed denominator (FixedTape.midBox ibox6)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox6).gradient k).lo.natAbs ((computed denominator ibox6).gradient k).hi.natAbs : Int)*((ibox6 k).hi-(ibox6 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox6
    (computed denominator ibox6) (computed denominator (FixedTape.midBox ibox6))
    (by decide +kernel)
private theorem midpoint_even_6 : ∀ k, 2 ∣ (ibox6 k).lo+(ibox6 k).hi := by decide +kernel
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox6 midpoint_even_6
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox6,candidate_valid h (FixedTape.midBox ibox6),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox6 106 (FixedTape.rowsAux denominator ibox6 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox6) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_6
private noncomputable def tree5 : TapeTree := .face 1 true (candidateRows ibox5) tree6
attribute [irreducible] tree5
private theorem sign_5 : 0 ≤ ((computed denominator ibox5).gradient 1).lo := by decide +kernel
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox5,?_,accepted_6 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox5)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox5).gradient 1).lo) denominator_positive).2 sign_5
private noncomputable def tree4 : TapeTree := .split 2 (((4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree7
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 2 (4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 : Int) false,decode_split denominator ibox4 2 (4083358450047562983570553510476258221271048822543336759818030794200387001091664754193273664307200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_7 h⟩
private noncomputable def tree3 : TapeTree := .centered (candidateRows ibox3) (candidateRows (FixedTape.midBox ibox3))
attribute [irreducible] tree3
private theorem sign_3 : 2*denominator*(computed denominator (FixedTape.midBox ibox3)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox3).gradient k).lo.natAbs ((computed denominator ibox3).gradient k).hi.natAbs : Int)*((ibox3 k).hi-(ibox3 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox3
    (computed denominator ibox3) (computed denominator (FixedTape.midBox ibox3))
    (by decide +kernel)
private theorem midpoint_even_3 : ∀ k, 2 ∣ (ibox3 k).lo+(ibox3 k).hi := by decide +kernel
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox3 midpoint_even_3
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox3,candidate_valid h (FixedTape.midBox ibox3),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox3 106 (FixedTape.rowsAux denominator ibox3 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox3) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_3
private noncomputable def tree2 : TapeTree := .face 1 true (candidateRows ibox2) tree3
attribute [irreducible] tree2
private theorem sign_2 : 0 ≤ ((computed denominator ibox2).gradient 1).lo := by decide +kernel
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox2,?_,accepted_3 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox2)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox2).gradient 1).lo) denominator_positive).2 sign_2
private noncomputable def tree1 : TapeTree := .split 2 (((2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree2 tree4
attribute [irreducible] tree1
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox1 2 (2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) false,decode_split denominator ibox1 2 (2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_2 h,accepted_4 h⟩
private noncomputable def tree0 : TapeTree := .split 1 (((2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree1 tree12
attribute [irreducible] tree0
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox0 1 (2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) false,decode_split denominator ibox0 1 (2722238966698375322380369006984172147514032548362224506545353862800258000727776502795515776204800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_1 h,accepted_12 h⟩
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (3333333333333333/10000000000000000 : ℚ) (11/32 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 106 = e114 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (3333333333333333/10000000000000000 : ℚ) (11/32 : ℚ)) x → eval e114 x ≤ 0 := by
  have hb := h.child_4 tape 106 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell51_low_internal

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell51_low_internal
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((3333333333333333/10000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((11/32 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 51 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 51 p)
    (hk0 : ((11/32 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((3333333333333333/10000000000000000 : ℚ) : ℝ))
    (hk1 : ((11/32 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((3333333333333333/10000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell51_low_internal.cell_bound h.child_8 h.child_9 (Cell51_low_internal.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell51_low_internal
