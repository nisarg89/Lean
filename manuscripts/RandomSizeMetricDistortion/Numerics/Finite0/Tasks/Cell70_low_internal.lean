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
namespace Cell70_low_internal
private noncomputable def qValues : Fin 4 → ℚ := ![(31208003653776233581644556680328034624/39175048602380164014911496848679027909 : ℚ),(51239704028900869596005000000000000000/39175048602380164014911496848679027909 : ℚ),(89111626557402529214748423895694898544/34105995039584759757437527906140570843 : ℚ),(-50676162778523279386670000000000000000/34105995039584759757437527906140570843 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics18.e2 qValues
private noncomputable abbrev e10 : PolyExpr := SharedFiniteSemantics18.e10 qValues
private noncomputable abbrev e11 : PolyExpr := SharedFiniteSemantics18.e11 qValues
private noncomputable abbrev e14 : PolyExpr := SharedFiniteSemantics18.e14 qValues
private noncomputable abbrev e16 : PolyExpr := SharedFiniteSemantics18.e16 qValues
private noncomputable abbrev e112 : PolyExpr := SharedFiniteSemantics18.e112 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics18.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics18.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics18.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics18.node_4 qValues
private noncomputable abbrev node_5 := SharedFiniteSemantics18.node_5 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics18.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics18.node_7 qValues
private noncomputable abbrev node_8 := SharedFiniteSemantics18.node_8 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics18.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics18.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics18.node_11 qValues
private noncomputable abbrev node_12 := SharedFiniteSemantics18.node_12 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics18.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics18.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics18.node_15 qValues
private noncomputable abbrev node_16 := SharedFiniteSemantics18.node_16 qValues
private noncomputable abbrev node_54 := SharedFiniteSemantics18.node_54 qValues
private noncomputable abbrev node_55 := SharedFiniteSemantics18.node_55 qValues
private noncomputable abbrev node_72 := SharedFiniteSemantics18.node_72 qValues
private noncomputable abbrev node_73 := SharedFiniteSemantics18.node_73 qValues
private noncomputable abbrev node_74 := SharedFiniteSemantics18.node_74 qValues
private noncomputable abbrev node_75 := SharedFiniteSemantics18.node_75 qValues
private noncomputable abbrev node_76 := SharedFiniteSemantics18.node_76 qValues
private noncomputable abbrev node_77 := SharedFiniteSemantics18.node_77 qValues
private noncomputable abbrev node_78 := SharedFiniteSemantics18.node_78 qValues
private noncomputable abbrev node_79 := SharedFiniteSemantics18.node_79 qValues
private noncomputable abbrev node_80 := SharedFiniteSemantics18.node_80 qValues
private noncomputable abbrev node_81 := SharedFiniteSemantics18.node_81 qValues
private noncomputable abbrev node_82 := SharedFiniteSemantics18.node_82 qValues
private noncomputable abbrev node_83 := SharedFiniteSemantics18.node_83 qValues
private noncomputable abbrev node_85 := SharedFiniteSemantics18.node_85 qValues
private noncomputable abbrev node_86 := SharedFiniteSemantics18.node_86 qValues
private noncomputable abbrev node_87 := SharedFiniteSemantics18.node_87 qValues
private noncomputable abbrev node_92 := SharedFiniteSemantics18.node_92 qValues
private noncomputable abbrev node_93 := SharedFiniteSemantics18.node_93 qValues
private noncomputable abbrev node_94 := SharedFiniteSemantics18.node_94 qValues
private noncomputable abbrev node_111 := SharedFiniteSemantics18.node_111 qValues
private noncomputable abbrev node_112 := SharedFiniteSemantics18.node_112 qValues
private noncomputable abbrev semantic_H_37 := SharedFiniteSemantics18.semantic_H_37 qValues
private noncomputable abbrev semantic_H_53 := SharedFiniteSemantics18.semantic_H_53 qValues
private noncomputable abbrev semantic_H_71 := SharedFiniteSemantics18.semantic_H_71 qValues
private noncomputable abbrev semantic_psi_110 := SharedFiniteSemantics18.semantic_psi_110 qValues
private noncomputable def aPoint (x : Fin 4 → ℝ) : ℝ := x 0*x 1
private noncomputable def rPoint (x : Fin 4 → ℝ) : ℝ := x 0+(((2840189/5000000 : ℚ) : ℝ)-x 0)*x 3
private noncomputable def capPoint (x : Fin 4 → ℝ) : ℝ := x 0+(rPoint x-x 0)*x 2
private noncomputable def yPoint (x : Fin 4 → ℝ) : ℝ := aPoint x+capPoint x-x 0
private theorem point_11 (x : Fin 4 → ℝ) : eval e11 x = aPoint x := by
  simp only [node_2,node_3,node_11] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_10 (x : Fin 4 → ℝ) : eval e10 x = rPoint x := by
  simp only [node_2,node_5,node_6,node_7,node_8,node_9,node_10] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_2 (x : Fin 4 → ℝ) : eval e2 x = x 0 := by
  simp only [node_2] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_14 (x : Fin 4 → ℝ) : eval e14 x = capPoint x := by
  simp only [node_2,node_4,node_5,node_6,node_7,node_8,node_9,node_10,node_12,node_13,node_14] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_16 (x : Fin 4 → ℝ) : eval e16 x = yPoint x := by
  simp only [node_2,node_3,node_4,node_5,node_6,node_7,node_8,node_9,node_10,node_11,node_12,node_13,node_14,node_15,node_16] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem price_lambda_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceLambda 70 p = ((31208003653776233581644556680328034624/39175048602380164014911496848679027909 : ℝ)+(51239704028900869596005000000000000000/39175048602380164014911496848679027909 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell70,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 70 p = (((89111626557402529214748423895694898544/34105995039584759757437527906140570843 : ℝ)+(-50676162778523279386670000000000000000/34105995039584759757437527906140570843 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell70,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e112 x = (x 0*(1-x 0))*(aPoint x+priceLambda 70 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 70 (x 0)*psiStar (rPoint x)+(0)-(0)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_7,node_54,node_55,node_72,node_73,node_74,node_75,node_76,node_77,node_78,node_79,node_80,node_81,node_82,node_83,node_85,node_86,node_87,node_92,node_93,node_94,node_111,node_112,semantic_H_37,semantic_H_53,semantic_H_71,semantic_psi_110,point_11,point_10,point_2,point_14,point_16]
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
    (hL : lambdaStar (x 0) = priceLambda 70 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 70 (x 0)) :
    (1)*eval e112 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,if_pos hA,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (1/2 : ℚ) (2552083333333333/5000000000000000 : ℚ)) x → eval e112 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((1/2 : ℚ) : ℝ) < p ∧ p ≤ ((2552083333333333/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 70 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 70 p)
    (hk0 : ((2552083333333333/5000000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((1/2 : ℚ) : ℝ))
    (hk1 : ((2552083333333333/5000000000000000 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((1/2 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h3 (1/2 : ℚ) (2552083333333333/5000000000000000 : ℚ) ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ) p a A r hpcell hk0 hk1 hr ha hap hpA hAr
  have hcut : ¬(((2552083333333333/5000000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ)) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint,if_neg hcut] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint,if_neg hcut] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint,if_neg hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 70 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 70 (x 0) := by simpa only [hxp] using hT
  have hrootb : ((2840189/5000000 : ℚ) : ℝ) ≤ bStar := by norm_num [bStar]
  have hAb : A ≤ bStar := hAr.trans (hr.2.trans hrootb)
  have hflag : aPoint x ≤ bStar := by rw [hax]; exact hap.trans (hpA.trans hAb)
  have hflagA : capPoint x ≤ bStar := by simpa only [hAx] using hAb
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e112 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
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
.const (2840189/5000000 : ℚ),
.neg 1,
.add 5 6,
.mul 7 4,
.add 1 8,
.mul 1 2,
.add 9 6,
.mul 11 3,
.add 1 12,
.add 10 13,
.add 14 6,
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
.mul 16 10,
.mul 10 10,
.mul 19 38,
.mul 10 38,
.mul 22 40,
.add 39 41,
.mul 38 38,
.mul 43 43,
.mul 44 44,
.mul 45 45,
.mul 10 46,
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
.const (31208003653776233581644556680328034624/39175048602380164014911496848679027909 : ℚ),
.const (51239704028900869596005000000000000000/39175048602380164014911496848679027909 : ℚ),
.mul 74 1,
.add 73 75,
.const (89111626557402529214748423895694898544/34105995039584759757437527906140570843 : ℚ),
.const (-50676162778523279386670000000000000000/34105995039584759757437527906140570843 : ℚ),
.mul 78 1,
.add 77 79,
.add 0 6,
.mul 1 81,
.const (-145513/100000 : ℚ),
.add 80 83,
.mul 84 82,
.mul 10 82,
.mul 76 72,
.add 86 87,
.const (19/73 : ℚ),
.mul 89 9,
.mul 9 9,
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
private noncomputable def ssaQVals : Fin 15 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(31208003653776233581644556680328034624/39175048602380164014911496848679027909 : ℚ),(51239704028900869596005000000000000000/39175048602380164014911496848679027909 : ℚ),(89111626557402529214748423895694898544/34105995039584759757437527906140570843 : ℚ),(-50676162778523279386670000000000000000/34105995039584759757437527906140570843 : ℚ),(-145513/100000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_5c7196fee7b05b99.p107 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_5c7196fee7b05b99.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 106 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_5c7196fee7b05b99.ssa_matches ssaQVals D B

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
private noncomputable def denominator : Int := 609248706992286112020770669500357806814607085610141278557438815928988292236379848340559625820569600000000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000,310970694193979329060687896405066829176911066589655823289887021621002536999731152324607826587259177296024945295360000000⟩,⟨0,609248706992286112020770669500357806814607085610141278557438815928988292236379848340559625820569600000000000000000000000⟩,⟨0,609248706992286112020770669500357806814607085610141278557438815928988292236379848340559625820569600000000000000000000000⟩,⟨0,609248706992286112020770669500357806814607085610141278557438815928988292236379848340559625820569600000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := splitI ibox0 1 304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 1 true
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 2 304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox2 2 304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 true
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox0 1 304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 true
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox5 1 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 false
private noncomputable def ibox7 : Fin 4 → FixedTape.I := faceI ibox6 1 true
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox7 2 304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 false
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox8 2 152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 false
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox8 2 152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 true
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox7 2 304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox11 2 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 false
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox11 2 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 true
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox5 1 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 true
private noncomputable def ibox15 : Fin 4 → FixedTape.I := faceI ibox14 1 true
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox15 2 304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 false
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 2 152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox17 3 304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 false
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox18 2 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 false
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 3 152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox20 2 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 false
private noncomputable def ibox22 : Fin 4 → FixedTape.I := faceI ibox21 3 false
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox20 2 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 true
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox23 3 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 false
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox23 3 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 true
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox19 3 152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 true
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox26 2 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 false
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox26 2 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 true
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox18 2 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 true
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox29 3 152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 false
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox30 2 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 false
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox31 3 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 false
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox32 2 95195110467544705003245417109430907314782357126584574774599814988904420661934351303212441534464000000000000000000000000 false
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox32 2 95195110467544705003245417109430907314782357126584574774599814988904420661934351303212441534464000000000000000000000000 true
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox31 3 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 true
private noncomputable def ibox36 : Fin 4 → FixedTape.I := splitI ibox30 2 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 true
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox36 3 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 false
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox37 2 133273154654562587004543583953203270240695299977218404684439740984466188926708091824497418148249600000000000000000000000 false
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox37 2 133273154654562587004543583953203270240695299977218404684439740984466188926708091824497418148249600000000000000000000000 true
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox36 3 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 true
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox29 3 152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 true
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox41 2 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 false
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox41 2 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 true
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox17 3 304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 true
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox44 2 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 false
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox45 2 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 false
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox45 2 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 true
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox47 3 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 false
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox47 3 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 true
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox44 2 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 true
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox50 3 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 false
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox51 2 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 false
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox51 2 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 true
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox50 3 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 true
private noncomputable def ibox55 : Fin 4 → FixedTape.I := splitI ibox54 2 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 false
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox54 2 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 true
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox16 2 152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 true
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox57 3 304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 false
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox58 2 228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 false
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox59 3 152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 false
private noncomputable def ibox61 : Fin 4 → FixedTape.I := splitI ibox60 2 190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 false
private noncomputable def ibox62 : Fin 4 → FixedTape.I := splitI ibox61 3 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 false
private noncomputable def ibox63 : Fin 4 → FixedTape.I := splitI ibox62 2 171351198841580469005841750796975633166608242827852234594279666980027957191481832345782394762035200000000000000000000000 false
private noncomputable def ibox64 : Fin 4 → FixedTape.I := splitI ibox62 2 171351198841580469005841750796975633166608242827852234594279666980027957191481832345782394762035200000000000000000000000 true
private noncomputable def ibox65 : Fin 4 → FixedTape.I := splitI ibox61 3 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 true
private noncomputable def ibox66 : Fin 4 → FixedTape.I := splitI ibox60 2 190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 true
private noncomputable def ibox67 : Fin 4 → FixedTape.I := splitI ibox66 3 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 false
private noncomputable def ibox68 : Fin 4 → FixedTape.I := splitI ibox67 2 209429243028598351007139917640747996092521185678486064504119592975589725456255572867067371375820800000000000000000000000 false
private noncomputable def ibox69 : Fin 4 → FixedTape.I := splitI ibox67 2 209429243028598351007139917640747996092521185678486064504119592975589725456255572867067371375820800000000000000000000000 true
private noncomputable def ibox70 : Fin 4 → FixedTape.I := splitI ibox66 3 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 true
private noncomputable def ibox71 : Fin 4 → FixedTape.I := splitI ibox59 3 152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 true
private noncomputable def ibox72 : Fin 4 → FixedTape.I := splitI ibox71 2 190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 false
private noncomputable def ibox73 : Fin 4 → FixedTape.I := splitI ibox72 3 228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 false
private noncomputable def ibox74 : Fin 4 → FixedTape.I := splitI ibox72 3 228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 true
private noncomputable def ibox75 : Fin 4 → FixedTape.I := splitI ibox71 2 190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 true
private noncomputable def ibox76 : Fin 4 → FixedTape.I := splitI ibox75 3 228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 false
private noncomputable def ibox77 : Fin 4 → FixedTape.I := splitI ibox75 3 228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 true
private noncomputable def ibox78 : Fin 4 → FixedTape.I := splitI ibox58 2 228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 true
private noncomputable def ibox79 : Fin 4 → FixedTape.I := splitI ibox78 3 152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 false
private noncomputable def ibox80 : Fin 4 → FixedTape.I := splitI ibox79 3 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 false
private noncomputable def ibox81 : Fin 4 → FixedTape.I := splitI ibox80 2 266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 false
private noncomputable def ibox82 : Fin 4 → FixedTape.I := splitI ibox81 3 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 false
private noncomputable def ibox83 : Fin 4 → FixedTape.I := splitI ibox81 3 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 true
private noncomputable def ibox84 : Fin 4 → FixedTape.I := splitI ibox80 2 266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 true
private noncomputable def ibox85 : Fin 4 → FixedTape.I := splitI ibox84 3 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 false
private noncomputable def ibox86 : Fin 4 → FixedTape.I := splitI ibox84 3 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 true
private noncomputable def ibox87 : Fin 4 → FixedTape.I := splitI ibox79 3 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 true
private noncomputable def ibox88 : Fin 4 → FixedTape.I := splitI ibox87 2 266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 false
private noncomputable def ibox89 : Fin 4 → FixedTape.I := splitI ibox87 2 266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 true
private noncomputable def ibox90 : Fin 4 → FixedTape.I := splitI ibox78 3 152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 true
private noncomputable def ibox91 : Fin 4 → FixedTape.I := splitI ibox90 2 266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 false
private noncomputable def ibox92 : Fin 4 → FixedTape.I := splitI ibox91 3 228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 false
private noncomputable def ibox93 : Fin 4 → FixedTape.I := splitI ibox91 3 228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 true
private noncomputable def ibox94 : Fin 4 → FixedTape.I := splitI ibox90 2 266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 true
private noncomputable def ibox95 : Fin 4 → FixedTape.I := splitI ibox94 3 228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 false
private noncomputable def ibox96 : Fin 4 → FixedTape.I := splitI ibox94 3 228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 true
private noncomputable def ibox97 : Fin 4 → FixedTape.I := splitI ibox57 3 304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 true
private noncomputable def ibox98 : Fin 4 → FixedTape.I := splitI ibox97 2 228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 false
private noncomputable def ibox99 : Fin 4 → FixedTape.I := splitI ibox98 3 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 false
private noncomputable def ibox100 : Fin 4 → FixedTape.I := splitI ibox99 2 190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 false
private noncomputable def ibox101 : Fin 4 → FixedTape.I := splitI ibox99 2 190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 true
private noncomputable def ibox102 : Fin 4 → FixedTape.I := splitI ibox98 3 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 true
private noncomputable def ibox103 : Fin 4 → FixedTape.I := splitI ibox102 2 190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 false
private noncomputable def ibox104 : Fin 4 → FixedTape.I := splitI ibox102 2 190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 true
private noncomputable def ibox105 : Fin 4 → FixedTape.I := splitI ibox97 2 228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 true
private noncomputable def ibox106 : Fin 4 → FixedTape.I := splitI ibox105 3 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 false
private noncomputable def ibox107 : Fin 4 → FixedTape.I := splitI ibox106 2 266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 false
private noncomputable def ibox108 : Fin 4 → FixedTape.I := splitI ibox106 2 266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 true
private noncomputable def ibox109 : Fin 4 → FixedTape.I := splitI ibox105 3 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 true
private noncomputable def ibox110 : Fin 4 → FixedTape.I := splitI ibox109 2 266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 false
private noncomputable def ibox111 : Fin 4 → FixedTape.I := splitI ibox109 2 266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 true
private noncomputable def ibox112 : Fin 4 → FixedTape.I := splitI ibox15 2 304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 true
private noncomputable def ibox113 : Fin 4 → FixedTape.I := splitI ibox112 3 304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 false
private noncomputable def ibox114 : Fin 4 → FixedTape.I := splitI ibox113 2 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 false
private noncomputable def ibox115 : Fin 4 → FixedTape.I := splitI ibox114 3 152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 false
private noncomputable def ibox116 : Fin 4 → FixedTape.I := splitI ibox115 2 380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 false
private noncomputable def ibox117 : Fin 4 → FixedTape.I := splitI ibox116 3 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 false
private noncomputable def ibox118 : Fin 4 → FixedTape.I := splitI ibox117 2 342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 false
private noncomputable def ibox119 : Fin 4 → FixedTape.I := splitI ibox118 3 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 false
private noncomputable def ibox120 : Fin 4 → FixedTape.I := splitI ibox118 3 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 true
private noncomputable def ibox121 : Fin 4 → FixedTape.I := splitI ibox117 2 342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 true
private noncomputable def ibox122 : Fin 4 → FixedTape.I := splitI ibox121 3 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 false
private noncomputable def ibox123 : Fin 4 → FixedTape.I := splitI ibox122 0 307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 false
private noncomputable def ibox124 : Fin 4 → FixedTape.I := splitI ibox122 0 307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 true
private noncomputable def ibox125 : Fin 4 → FixedTape.I := splitI ibox121 3 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 true
private noncomputable def ibox126 : Fin 4 → FixedTape.I := splitI ibox116 3 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 true
private noncomputable def ibox127 : Fin 4 → FixedTape.I := splitI ibox126 2 342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 false
private noncomputable def ibox128 : Fin 4 → FixedTape.I := splitI ibox127 3 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 false
private noncomputable def ibox129 : Fin 4 → FixedTape.I := splitI ibox127 3 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 true
private noncomputable def ibox130 : Fin 4 → FixedTape.I := splitI ibox126 2 342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 true
private noncomputable def ibox131 : Fin 4 → FixedTape.I := splitI ibox130 3 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 false
private noncomputable def ibox132 : Fin 4 → FixedTape.I := splitI ibox130 3 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 true
private noncomputable def ibox133 : Fin 4 → FixedTape.I := splitI ibox115 2 380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 true
private noncomputable def ibox134 : Fin 4 → FixedTape.I := splitI ibox133 3 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 false
private noncomputable def ibox135 : Fin 4 → FixedTape.I := splitI ibox134 2 418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 false
private noncomputable def ibox136 : Fin 4 → FixedTape.I := splitI ibox135 3 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 false
private noncomputable def ibox137 : Fin 4 → FixedTape.I := splitI ibox136 0 307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 false
private noncomputable def ibox138 : Fin 4 → FixedTape.I := splitI ibox136 0 307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 true
private noncomputable def ibox139 : Fin 4 → FixedTape.I := splitI ibox135 3 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 true
private noncomputable def ibox140 : Fin 4 → FixedTape.I := splitI ibox134 2 418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 true
private noncomputable def ibox141 : Fin 4 → FixedTape.I := splitI ibox140 3 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 false
private noncomputable def ibox142 : Fin 4 → FixedTape.I := splitI ibox141 0 307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 false
private noncomputable def ibox143 : Fin 4 → FixedTape.I := splitI ibox141 0 307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 true
private noncomputable def ibox144 : Fin 4 → FixedTape.I := splitI ibox140 3 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 true
private noncomputable def ibox145 : Fin 4 → FixedTape.I := splitI ibox133 3 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 true
private noncomputable def ibox146 : Fin 4 → FixedTape.I := splitI ibox145 2 418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 false
private noncomputable def ibox147 : Fin 4 → FixedTape.I := splitI ibox146 3 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 false
private noncomputable def ibox148 : Fin 4 → FixedTape.I := splitI ibox146 3 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 true
private noncomputable def ibox149 : Fin 4 → FixedTape.I := splitI ibox145 2 418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 true
private noncomputable def ibox150 : Fin 4 → FixedTape.I := splitI ibox149 3 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 false
private noncomputable def ibox151 : Fin 4 → FixedTape.I := splitI ibox149 3 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 true
private noncomputable def ibox152 : Fin 4 → FixedTape.I := splitI ibox114 3 152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 true
private noncomputable def ibox153 : Fin 4 → FixedTape.I := splitI ibox152 2 380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 false
private noncomputable def ibox154 : Fin 4 → FixedTape.I := splitI ibox153 3 228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 false
private noncomputable def ibox155 : Fin 4 → FixedTape.I := splitI ibox154 2 342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 false
private noncomputable def ibox156 : Fin 4 → FixedTape.I := splitI ibox154 2 342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 true
private noncomputable def ibox157 : Fin 4 → FixedTape.I := splitI ibox153 3 228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 true
private noncomputable def ibox158 : Fin 4 → FixedTape.I := splitI ibox157 2 342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 false
private noncomputable def ibox159 : Fin 4 → FixedTape.I := splitI ibox157 2 342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 true
private noncomputable def ibox160 : Fin 4 → FixedTape.I := splitI ibox152 2 380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 true
private noncomputable def ibox161 : Fin 4 → FixedTape.I := splitI ibox160 3 228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 false
private noncomputable def ibox162 : Fin 4 → FixedTape.I := splitI ibox161 2 418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 false
private noncomputable def ibox163 : Fin 4 → FixedTape.I := splitI ibox161 2 418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 true
private noncomputable def ibox164 : Fin 4 → FixedTape.I := splitI ibox160 3 228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 true
private noncomputable def ibox165 : Fin 4 → FixedTape.I := splitI ibox164 2 418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 false
private noncomputable def ibox166 : Fin 4 → FixedTape.I := splitI ibox164 2 418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 true
private noncomputable def ibox167 : Fin 4 → FixedTape.I := splitI ibox113 2 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 true
private noncomputable def ibox168 : Fin 4 → FixedTape.I := splitI ibox167 3 152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 false
private noncomputable def ibox169 : Fin 4 → FixedTape.I := splitI ibox168 2 533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 false
private noncomputable def ibox170 : Fin 4 → FixedTape.I := splitI ibox169 3 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 false
private noncomputable def ibox171 : Fin 4 → FixedTape.I := splitI ibox170 2 495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 false
private noncomputable def ibox172 : Fin 4 → FixedTape.I := splitI ibox171 3 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 false
private noncomputable def ibox173 : Fin 4 → FixedTape.I := splitI ibox172 0 307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 false
private noncomputable def ibox174 : Fin 4 → FixedTape.I := splitI ibox172 0 307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 true
private noncomputable def ibox175 : Fin 4 → FixedTape.I := splitI ibox171 3 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 true
private noncomputable def ibox176 : Fin 4 → FixedTape.I := splitI ibox170 2 495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 true
private noncomputable def ibox177 : Fin 4 → FixedTape.I := splitI ibox176 3 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 false
private noncomputable def ibox178 : Fin 4 → FixedTape.I := splitI ibox177 0 307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 false
private noncomputable def ibox179 : Fin 4 → FixedTape.I := splitI ibox177 0 307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 true
private noncomputable def ibox180 : Fin 4 → FixedTape.I := splitI ibox176 3 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 true
private noncomputable def ibox181 : Fin 4 → FixedTape.I := splitI ibox180 0 307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 false
private noncomputable def ibox182 : Fin 4 → FixedTape.I := splitI ibox180 0 307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 true
private noncomputable def ibox183 : Fin 4 → FixedTape.I := splitI ibox169 3 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 true
private noncomputable def ibox184 : Fin 4 → FixedTape.I := splitI ibox183 2 495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 false
private noncomputable def ibox185 : Fin 4 → FixedTape.I := splitI ibox184 3 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 false
private noncomputable def ibox186 : Fin 4 → FixedTape.I := splitI ibox184 3 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 true
private noncomputable def ibox187 : Fin 4 → FixedTape.I := splitI ibox183 2 495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 true
private noncomputable def ibox188 : Fin 4 → FixedTape.I := splitI ibox187 3 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 false
private noncomputable def ibox189 : Fin 4 → FixedTape.I := splitI ibox187 3 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 true
private noncomputable def ibox190 : Fin 4 → FixedTape.I := splitI ibox168 2 533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 true
private noncomputable def ibox191 : Fin 4 → FixedTape.I := splitI ibox190 3 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 false
private noncomputable def ibox192 : Fin 4 → FixedTape.I := splitI ibox191 2 571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 false
private noncomputable def ibox193 : Fin 4 → FixedTape.I := splitI ibox192 3 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 false
private noncomputable def ibox194 : Fin 4 → FixedTape.I := splitI ibox193 0 307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 false
private noncomputable def ibox195 : Fin 4 → FixedTape.I := splitI ibox193 0 307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 true
private noncomputable def ibox196 : Fin 4 → FixedTape.I := splitI ibox192 3 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 true
private noncomputable def ibox197 : Fin 4 → FixedTape.I := splitI ibox196 0 307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 false
private noncomputable def ibox198 : Fin 4 → FixedTape.I := splitI ibox196 0 307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 true
private noncomputable def ibox199 : Fin 4 → FixedTape.I := splitI ibox191 2 571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 true
private noncomputable def ibox200 : Fin 4 → FixedTape.I := splitI ibox199 3 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 false
private noncomputable def ibox201 : Fin 4 → FixedTape.I := splitI ibox200 0 307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 false
private noncomputable def ibox202 : Fin 4 → FixedTape.I := splitI ibox200 0 307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 true
private noncomputable def ibox203 : Fin 4 → FixedTape.I := splitI ibox199 3 38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 true
private noncomputable def ibox204 : Fin 4 → FixedTape.I := splitI ibox203 0 307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 false
private noncomputable def ibox205 : Fin 4 → FixedTape.I := splitI ibox203 0 307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 true
private noncomputable def ibox206 : Fin 4 → FixedTape.I := splitI ibox190 3 76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 true
private noncomputable def ibox207 : Fin 4 → FixedTape.I := splitI ibox206 2 571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 false
private noncomputable def ibox208 : Fin 4 → FixedTape.I := splitI ibox207 3 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 false
private noncomputable def ibox209 : Fin 4 → FixedTape.I := splitI ibox207 3 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 true
private noncomputable def ibox210 : Fin 4 → FixedTape.I := splitI ibox206 2 571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 true
private noncomputable def ibox211 : Fin 4 → FixedTape.I := splitI ibox210 3 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 false
private noncomputable def ibox212 : Fin 4 → FixedTape.I := splitI ibox210 3 114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 true
private noncomputable def ibox213 : Fin 4 → FixedTape.I := splitI ibox167 3 152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 true
private noncomputable def ibox214 : Fin 4 → FixedTape.I := splitI ibox213 2 533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 false
private noncomputable def ibox215 : Fin 4 → FixedTape.I := splitI ibox214 3 228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 false
private noncomputable def ibox216 : Fin 4 → FixedTape.I := splitI ibox215 2 495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 false
private noncomputable def ibox217 : Fin 4 → FixedTape.I := splitI ibox216 3 190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 false
private noncomputable def ibox218 : Fin 4 → FixedTape.I := splitI ibox216 3 190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 true
private noncomputable def ibox219 : Fin 4 → FixedTape.I := splitI ibox215 2 495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 true
private noncomputable def ibox220 : Fin 4 → FixedTape.I := splitI ibox219 3 190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 false
private noncomputable def ibox221 : Fin 4 → FixedTape.I := splitI ibox219 3 190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 true
private noncomputable def ibox222 : Fin 4 → FixedTape.I := splitI ibox214 3 228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 true
private noncomputable def ibox223 : Fin 4 → FixedTape.I := splitI ibox222 2 495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 false
private noncomputable def ibox224 : Fin 4 → FixedTape.I := splitI ibox222 2 495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 true
private noncomputable def ibox225 : Fin 4 → FixedTape.I := splitI ibox213 2 533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 true
private noncomputable def ibox226 : Fin 4 → FixedTape.I := splitI ibox225 3 228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 false
private noncomputable def ibox227 : Fin 4 → FixedTape.I := splitI ibox226 2 571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 false
private noncomputable def ibox228 : Fin 4 → FixedTape.I := splitI ibox227 3 190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 false
private noncomputable def ibox229 : Fin 4 → FixedTape.I := splitI ibox227 3 190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 true
private noncomputable def ibox230 : Fin 4 → FixedTape.I := splitI ibox226 2 571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 true
private noncomputable def ibox231 : Fin 4 → FixedTape.I := splitI ibox230 3 190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 false
private noncomputable def ibox232 : Fin 4 → FixedTape.I := splitI ibox230 3 190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 true
private noncomputable def ibox233 : Fin 4 → FixedTape.I := splitI ibox225 3 228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 true
private noncomputable def ibox234 : Fin 4 → FixedTape.I := splitI ibox233 2 571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 false
private noncomputable def ibox235 : Fin 4 → FixedTape.I := splitI ibox233 2 571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 true
private noncomputable def ibox236 : Fin 4 → FixedTape.I := splitI ibox112 3 304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 true
private noncomputable def ibox237 : Fin 4 → FixedTape.I := splitI ibox236 2 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 false
private noncomputable def ibox238 : Fin 4 → FixedTape.I := splitI ibox237 2 380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 false
private noncomputable def ibox239 : Fin 4 → FixedTape.I := splitI ibox238 3 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 false
private noncomputable def ibox240 : Fin 4 → FixedTape.I := splitI ibox239 2 342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 false
private noncomputable def ibox241 : Fin 4 → FixedTape.I := splitI ibox240 3 380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 false
private noncomputable def ibox242 : Fin 4 → FixedTape.I := splitI ibox240 3 380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 true
private noncomputable def ibox243 : Fin 4 → FixedTape.I := splitI ibox239 2 342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 true
private noncomputable def ibox244 : Fin 4 → FixedTape.I := splitI ibox243 3 380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 false
private noncomputable def ibox245 : Fin 4 → FixedTape.I := splitI ibox243 3 380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 true
private noncomputable def ibox246 : Fin 4 → FixedTape.I := splitI ibox238 3 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 true
private noncomputable def ibox247 : Fin 4 → FixedTape.I := splitI ibox246 2 342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 false
private noncomputable def ibox248 : Fin 4 → FixedTape.I := splitI ibox246 2 342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 true
private noncomputable def ibox249 : Fin 4 → FixedTape.I := splitI ibox237 2 380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 true
private noncomputable def ibox250 : Fin 4 → FixedTape.I := splitI ibox249 3 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 false
private noncomputable def ibox251 : Fin 4 → FixedTape.I := splitI ibox250 3 380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 false
private noncomputable def ibox252 : Fin 4 → FixedTape.I := splitI ibox251 2 418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 false
private noncomputable def ibox253 : Fin 4 → FixedTape.I := splitI ibox251 2 418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 true
private noncomputable def ibox254 : Fin 4 → FixedTape.I := splitI ibox250 3 380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 true
private noncomputable def ibox255 : Fin 4 → FixedTape.I := splitI ibox254 2 418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 false
private noncomputable def ibox256 : Fin 4 → FixedTape.I := splitI ibox254 2 418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 true
private noncomputable def ibox257 : Fin 4 → FixedTape.I := splitI ibox249 3 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 true
private noncomputable def ibox258 : Fin 4 → FixedTape.I := splitI ibox257 2 418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 false
private noncomputable def ibox259 : Fin 4 → FixedTape.I := splitI ibox257 2 418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 true
private noncomputable def ibox260 : Fin 4 → FixedTape.I := splitI ibox236 2 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 true
private noncomputable def ibox261 : Fin 4 → FixedTape.I := splitI ibox260 3 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 false
private noncomputable def ibox262 : Fin 4 → FixedTape.I := splitI ibox261 2 533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 false
private noncomputable def ibox263 : Fin 4 → FixedTape.I := splitI ibox262 3 380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 false
private noncomputable def ibox264 : Fin 4 → FixedTape.I := splitI ibox263 2 495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 false
private noncomputable def ibox265 : Fin 4 → FixedTape.I := splitI ibox263 2 495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 true
private noncomputable def ibox266 : Fin 4 → FixedTape.I := splitI ibox262 3 380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 true
private noncomputable def ibox267 : Fin 4 → FixedTape.I := splitI ibox266 2 495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 false
private noncomputable def ibox268 : Fin 4 → FixedTape.I := splitI ibox266 2 495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 true
private noncomputable def ibox269 : Fin 4 → FixedTape.I := splitI ibox261 2 533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 true
private noncomputable def ibox270 : Fin 4 → FixedTape.I := splitI ibox269 3 380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 false
private noncomputable def ibox271 : Fin 4 → FixedTape.I := splitI ibox270 2 571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 false
private noncomputable def ibox272 : Fin 4 → FixedTape.I := splitI ibox270 2 571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 true
private noncomputable def ibox273 : Fin 4 → FixedTape.I := splitI ibox269 3 380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 true
private noncomputable def ibox274 : Fin 4 → FixedTape.I := splitI ibox273 2 571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 false
private noncomputable def ibox275 : Fin 4 → FixedTape.I := splitI ibox273 2 571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 true
private noncomputable def ibox276 : Fin 4 → FixedTape.I := splitI ibox260 3 456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 true
private noncomputable def ibox277 : Fin 4 → FixedTape.I := splitI ibox276 2 533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 false
private noncomputable def ibox278 : Fin 4 → FixedTape.I := splitI ibox277 3 533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 false
private noncomputable def ibox279 : Fin 4 → FixedTape.I := splitI ibox278 2 495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 false
private noncomputable def ibox280 : Fin 4 → FixedTape.I := splitI ibox278 2 495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 true
private noncomputable def ibox281 : Fin 4 → FixedTape.I := splitI ibox277 3 533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 true
private noncomputable def ibox282 : Fin 4 → FixedTape.I := splitI ibox276 2 533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 true
private noncomputable def ibox283 : Fin 4 → FixedTape.I := splitI ibox282 3 533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 false
private noncomputable def ibox284 : Fin 4 → FixedTape.I := splitI ibox283 2 571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 false
private noncomputable def ibox285 : Fin 4 → FixedTape.I := splitI ibox283 2 571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 true
private noncomputable def ibox286 : Fin 4 → FixedTape.I := splitI ibox282 3 533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 true
private noncomputable def tree286 : TapeTree := .centered (candidateRows ibox286) (candidateRows (FixedTape.midBox ibox286))
attribute [irreducible] tree286
private theorem sign_286 : 2*denominator*(computed denominator (FixedTape.midBox ibox286)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox286).gradient k).lo.natAbs ((computed denominator ibox286).gradient k).hi.natAbs : Int)*((ibox286 k).hi-(ibox286 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox286
    (computed denominator ibox286) (computed denominator (FixedTape.midBox ibox286))
    (by decide +kernel)
private theorem midpoint_even_286 : ∀ k, 2 ∣ (ibox286 k).lo+(ibox286 k).hi := by decide +kernel
private theorem accepted_286 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox286) tree286 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox286 midpoint_even_286
  simp only [tree286,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox286,candidate_valid h (FixedTape.midBox ibox286),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox286 106 (FixedTape.rowsAux denominator ibox286 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox286) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_286
private noncomputable def tree285 : TapeTree := .centered (candidateRows ibox285) (candidateRows (FixedTape.midBox ibox285))
attribute [irreducible] tree285
private theorem sign_285 : 2*denominator*(computed denominator (FixedTape.midBox ibox285)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox285).gradient k).lo.natAbs ((computed denominator ibox285).gradient k).hi.natAbs : Int)*((ibox285 k).hi-(ibox285 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox285
    (computed denominator ibox285) (computed denominator (FixedTape.midBox ibox285))
    (by decide +kernel)
private theorem midpoint_even_285 : ∀ k, 2 ∣ (ibox285 k).lo+(ibox285 k).hi := by decide +kernel
private theorem accepted_285 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox285) tree285 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox285 midpoint_even_285
  simp only [tree285,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox285,candidate_valid h (FixedTape.midBox ibox285),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox285 106 (FixedTape.rowsAux denominator ibox285 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox285) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_285
private noncomputable def tree284 : TapeTree := .centered (candidateRows ibox284) (candidateRows (FixedTape.midBox ibox284))
attribute [irreducible] tree284
private theorem sign_284 : 2*denominator*(computed denominator (FixedTape.midBox ibox284)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox284).gradient k).lo.natAbs ((computed denominator ibox284).gradient k).hi.natAbs : Int)*((ibox284 k).hi-(ibox284 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox284
    (computed denominator ibox284) (computed denominator (FixedTape.midBox ibox284))
    (by decide +kernel)
private theorem midpoint_even_284 : ∀ k, 2 ∣ (ibox284 k).lo+(ibox284 k).hi := by decide +kernel
private theorem accepted_284 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox284) tree284 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox284 midpoint_even_284
  simp only [tree284,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox284,candidate_valid h (FixedTape.midBox ibox284),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox284 106 (FixedTape.rowsAux denominator ibox284 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox284) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_284
private noncomputable def tree283 : TapeTree := .split 2 (((571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree284 tree285
attribute [irreducible] tree283
private theorem accepted_283 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox283) tree283 = true := by
  simp only [tree283,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox283 2 (571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) false,decode_split denominator ibox283 2 (571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_284 h,accepted_285 h⟩
private noncomputable def tree282 : TapeTree := .split 3 (((533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree283 tree286
attribute [irreducible] tree282
private theorem accepted_282 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox282) tree282 = true := by
  simp only [tree282,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox282 3 (533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 : Int) false,decode_split denominator ibox282 3 (533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_283 h,accepted_286 h⟩
private noncomputable def tree281 : TapeTree := .centered (candidateRows ibox281) (candidateRows (FixedTape.midBox ibox281))
attribute [irreducible] tree281
private theorem sign_281 : 2*denominator*(computed denominator (FixedTape.midBox ibox281)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox281).gradient k).lo.natAbs ((computed denominator ibox281).gradient k).hi.natAbs : Int)*((ibox281 k).hi-(ibox281 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox281
    (computed denominator ibox281) (computed denominator (FixedTape.midBox ibox281))
    (by decide +kernel)
private theorem midpoint_even_281 : ∀ k, 2 ∣ (ibox281 k).lo+(ibox281 k).hi := by decide +kernel
private theorem accepted_281 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox281) tree281 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox281 midpoint_even_281
  simp only [tree281,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox281,candidate_valid h (FixedTape.midBox ibox281),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox281 106 (FixedTape.rowsAux denominator ibox281 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox281) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_281
private noncomputable def tree280 : TapeTree := .centered (candidateRows ibox280) (candidateRows (FixedTape.midBox ibox280))
attribute [irreducible] tree280
private theorem sign_280 : 2*denominator*(computed denominator (FixedTape.midBox ibox280)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox280).gradient k).lo.natAbs ((computed denominator ibox280).gradient k).hi.natAbs : Int)*((ibox280 k).hi-(ibox280 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox280
    (computed denominator ibox280) (computed denominator (FixedTape.midBox ibox280))
    (by decide +kernel)
private theorem midpoint_even_280 : ∀ k, 2 ∣ (ibox280 k).lo+(ibox280 k).hi := by decide +kernel
private theorem accepted_280 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox280) tree280 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox280 midpoint_even_280
  simp only [tree280,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox280,candidate_valid h (FixedTape.midBox ibox280),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox280 106 (FixedTape.rowsAux denominator ibox280 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox280) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_280
private noncomputable def tree279 : TapeTree := .centered (candidateRows ibox279) (candidateRows (FixedTape.midBox ibox279))
attribute [irreducible] tree279
private theorem sign_279 : 2*denominator*(computed denominator (FixedTape.midBox ibox279)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox279).gradient k).lo.natAbs ((computed denominator ibox279).gradient k).hi.natAbs : Int)*((ibox279 k).hi-(ibox279 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox279
    (computed denominator ibox279) (computed denominator (FixedTape.midBox ibox279))
    (by decide +kernel)
private theorem midpoint_even_279 : ∀ k, 2 ∣ (ibox279 k).lo+(ibox279 k).hi := by decide +kernel
private theorem accepted_279 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox279) tree279 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox279 midpoint_even_279
  simp only [tree279,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox279,candidate_valid h (FixedTape.midBox ibox279),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox279 106 (FixedTape.rowsAux denominator ibox279 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox279) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_279
private noncomputable def tree278 : TapeTree := .split 2 (((495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree279 tree280
attribute [irreducible] tree278
private theorem accepted_278 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox278) tree278 = true := by
  simp only [tree278,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox278 2 (495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) false,decode_split denominator ibox278 2 (495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_279 h,accepted_280 h⟩
private noncomputable def tree277 : TapeTree := .split 3 (((533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree278 tree281
attribute [irreducible] tree277
private theorem accepted_277 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox277) tree277 = true := by
  simp only [tree277,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox277 3 (533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 : Int) false,decode_split denominator ibox277 3 (533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_278 h,accepted_281 h⟩
private noncomputable def tree276 : TapeTree := .split 2 (((533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree277 tree282
attribute [irreducible] tree276
private theorem accepted_276 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox276) tree276 = true := by
  simp only [tree276,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox276 2 (533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 : Int) false,decode_split denominator ibox276 2 (533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_277 h,accepted_282 h⟩
private noncomputable def tree275 : TapeTree := .centered (candidateRows ibox275) (candidateRows (FixedTape.midBox ibox275))
attribute [irreducible] tree275
private theorem sign_275 : 2*denominator*(computed denominator (FixedTape.midBox ibox275)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox275).gradient k).lo.natAbs ((computed denominator ibox275).gradient k).hi.natAbs : Int)*((ibox275 k).hi-(ibox275 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox275
    (computed denominator ibox275) (computed denominator (FixedTape.midBox ibox275))
    (by decide +kernel)
private theorem midpoint_even_275 : ∀ k, 2 ∣ (ibox275 k).lo+(ibox275 k).hi := by decide +kernel
private theorem accepted_275 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox275) tree275 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox275 midpoint_even_275
  simp only [tree275,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox275,candidate_valid h (FixedTape.midBox ibox275),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox275 106 (FixedTape.rowsAux denominator ibox275 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox275) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_275
private noncomputable def tree274 : TapeTree := .centered (candidateRows ibox274) (candidateRows (FixedTape.midBox ibox274))
attribute [irreducible] tree274
private theorem sign_274 : 2*denominator*(computed denominator (FixedTape.midBox ibox274)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox274).gradient k).lo.natAbs ((computed denominator ibox274).gradient k).hi.natAbs : Int)*((ibox274 k).hi-(ibox274 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox274
    (computed denominator ibox274) (computed denominator (FixedTape.midBox ibox274))
    (by decide +kernel)
private theorem midpoint_even_274 : ∀ k, 2 ∣ (ibox274 k).lo+(ibox274 k).hi := by decide +kernel
private theorem accepted_274 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox274) tree274 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox274 midpoint_even_274
  simp only [tree274,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox274,candidate_valid h (FixedTape.midBox ibox274),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox274 106 (FixedTape.rowsAux denominator ibox274 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox274) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_274
private noncomputable def tree273 : TapeTree := .split 2 (((571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree274 tree275
attribute [irreducible] tree273
private theorem accepted_273 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox273) tree273 = true := by
  simp only [tree273,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox273 2 (571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) false,decode_split denominator ibox273 2 (571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_274 h,accepted_275 h⟩
private noncomputable def tree272 : TapeTree := .centered (candidateRows ibox272) (candidateRows (FixedTape.midBox ibox272))
attribute [irreducible] tree272
private theorem sign_272 : 2*denominator*(computed denominator (FixedTape.midBox ibox272)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox272).gradient k).lo.natAbs ((computed denominator ibox272).gradient k).hi.natAbs : Int)*((ibox272 k).hi-(ibox272 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox272
    (computed denominator ibox272) (computed denominator (FixedTape.midBox ibox272))
    (by decide +kernel)
private theorem midpoint_even_272 : ∀ k, 2 ∣ (ibox272 k).lo+(ibox272 k).hi := by decide +kernel
private theorem accepted_272 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox272) tree272 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox272 midpoint_even_272
  simp only [tree272,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox272,candidate_valid h (FixedTape.midBox ibox272),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox272 106 (FixedTape.rowsAux denominator ibox272 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox272) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_272
private noncomputable def tree271 : TapeTree := .centered (candidateRows ibox271) (candidateRows (FixedTape.midBox ibox271))
attribute [irreducible] tree271
private theorem sign_271 : 2*denominator*(computed denominator (FixedTape.midBox ibox271)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox271).gradient k).lo.natAbs ((computed denominator ibox271).gradient k).hi.natAbs : Int)*((ibox271 k).hi-(ibox271 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox271
    (computed denominator ibox271) (computed denominator (FixedTape.midBox ibox271))
    (by decide +kernel)
private theorem midpoint_even_271 : ∀ k, 2 ∣ (ibox271 k).lo+(ibox271 k).hi := by decide +kernel
private theorem accepted_271 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox271) tree271 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox271 midpoint_even_271
  simp only [tree271,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox271,candidate_valid h (FixedTape.midBox ibox271),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox271 106 (FixedTape.rowsAux denominator ibox271 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox271) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_271
private noncomputable def tree270 : TapeTree := .split 2 (((571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree271 tree272
attribute [irreducible] tree270
private theorem accepted_270 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox270) tree270 = true := by
  simp only [tree270,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox270 2 (571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) false,decode_split denominator ibox270 2 (571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_271 h,accepted_272 h⟩
private noncomputable def tree269 : TapeTree := .split 3 (((380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree270 tree273
attribute [irreducible] tree269
private theorem accepted_269 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox269) tree269 = true := by
  simp only [tree269,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox269 3 (380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) false,decode_split denominator ibox269 3 (380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_270 h,accepted_273 h⟩
private noncomputable def tree268 : TapeTree := .centered (candidateRows ibox268) (candidateRows (FixedTape.midBox ibox268))
attribute [irreducible] tree268
private theorem sign_268 : 2*denominator*(computed denominator (FixedTape.midBox ibox268)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox268).gradient k).lo.natAbs ((computed denominator ibox268).gradient k).hi.natAbs : Int)*((ibox268 k).hi-(ibox268 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox268
    (computed denominator ibox268) (computed denominator (FixedTape.midBox ibox268))
    (by decide +kernel)
private theorem midpoint_even_268 : ∀ k, 2 ∣ (ibox268 k).lo+(ibox268 k).hi := by decide +kernel
private theorem accepted_268 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox268) tree268 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox268 midpoint_even_268
  simp only [tree268,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox268,candidate_valid h (FixedTape.midBox ibox268),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox268 106 (FixedTape.rowsAux denominator ibox268 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox268) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_268
private noncomputable def tree267 : TapeTree := .centered (candidateRows ibox267) (candidateRows (FixedTape.midBox ibox267))
attribute [irreducible] tree267
private theorem sign_267 : 2*denominator*(computed denominator (FixedTape.midBox ibox267)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox267).gradient k).lo.natAbs ((computed denominator ibox267).gradient k).hi.natAbs : Int)*((ibox267 k).hi-(ibox267 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox267
    (computed denominator ibox267) (computed denominator (FixedTape.midBox ibox267))
    (by decide +kernel)
private theorem midpoint_even_267 : ∀ k, 2 ∣ (ibox267 k).lo+(ibox267 k).hi := by decide +kernel
private theorem accepted_267 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox267) tree267 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox267 midpoint_even_267
  simp only [tree267,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox267,candidate_valid h (FixedTape.midBox ibox267),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox267 106 (FixedTape.rowsAux denominator ibox267 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox267) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_267
private noncomputable def tree266 : TapeTree := .split 2 (((495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree267 tree268
attribute [irreducible] tree266
private theorem accepted_266 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox266) tree266 = true := by
  simp only [tree266,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox266 2 (495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) false,decode_split denominator ibox266 2 (495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_267 h,accepted_268 h⟩
private noncomputable def tree265 : TapeTree := .centered (candidateRows ibox265) (candidateRows (FixedTape.midBox ibox265))
attribute [irreducible] tree265
private theorem sign_265 : 2*denominator*(computed denominator (FixedTape.midBox ibox265)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox265).gradient k).lo.natAbs ((computed denominator ibox265).gradient k).hi.natAbs : Int)*((ibox265 k).hi-(ibox265 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox265
    (computed denominator ibox265) (computed denominator (FixedTape.midBox ibox265))
    (by decide +kernel)
private theorem midpoint_even_265 : ∀ k, 2 ∣ (ibox265 k).lo+(ibox265 k).hi := by decide +kernel
private theorem accepted_265 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox265) tree265 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox265 midpoint_even_265
  simp only [tree265,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox265,candidate_valid h (FixedTape.midBox ibox265),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox265 106 (FixedTape.rowsAux denominator ibox265 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox265) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_265
private noncomputable def tree264 : TapeTree := .centered (candidateRows ibox264) (candidateRows (FixedTape.midBox ibox264))
attribute [irreducible] tree264
private theorem sign_264 : 2*denominator*(computed denominator (FixedTape.midBox ibox264)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox264).gradient k).lo.natAbs ((computed denominator ibox264).gradient k).hi.natAbs : Int)*((ibox264 k).hi-(ibox264 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox264
    (computed denominator ibox264) (computed denominator (FixedTape.midBox ibox264))
    (by decide +kernel)
private theorem midpoint_even_264 : ∀ k, 2 ∣ (ibox264 k).lo+(ibox264 k).hi := by decide +kernel
private theorem accepted_264 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox264) tree264 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox264 midpoint_even_264
  simp only [tree264,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox264,candidate_valid h (FixedTape.midBox ibox264),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox264 106 (FixedTape.rowsAux denominator ibox264 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox264) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_264
private noncomputable def tree263 : TapeTree := .split 2 (((495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree264 tree265
attribute [irreducible] tree263
private theorem accepted_263 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox263) tree263 = true := by
  simp only [tree263,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox263 2 (495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) false,decode_split denominator ibox263 2 (495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_264 h,accepted_265 h⟩
private noncomputable def tree262 : TapeTree := .split 3 (((380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree263 tree266
attribute [irreducible] tree262
private theorem accepted_262 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox262) tree262 = true := by
  simp only [tree262,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox262 3 (380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) false,decode_split denominator ibox262 3 (380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_263 h,accepted_266 h⟩
private noncomputable def tree261 : TapeTree := .split 2 (((533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree262 tree269
attribute [irreducible] tree261
private theorem accepted_261 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox261) tree261 = true := by
  simp only [tree261,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox261 2 (533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 : Int) false,decode_split denominator ibox261 2 (533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_262 h,accepted_269 h⟩
private noncomputable def tree260 : TapeTree := .split 3 (((456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree261 tree276
attribute [irreducible] tree260
private theorem accepted_260 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox260) tree260 = true := by
  simp only [tree260,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox260 3 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) false,decode_split denominator ibox260 3 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_261 h,accepted_276 h⟩
private noncomputable def tree259 : TapeTree := .centered (candidateRows ibox259) (candidateRows (FixedTape.midBox ibox259))
attribute [irreducible] tree259
private theorem sign_259 : 2*denominator*(computed denominator (FixedTape.midBox ibox259)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox259).gradient k).lo.natAbs ((computed denominator ibox259).gradient k).hi.natAbs : Int)*((ibox259 k).hi-(ibox259 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox259
    (computed denominator ibox259) (computed denominator (FixedTape.midBox ibox259))
    (by decide +kernel)
private theorem midpoint_even_259 : ∀ k, 2 ∣ (ibox259 k).lo+(ibox259 k).hi := by decide +kernel
private theorem accepted_259 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox259) tree259 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox259 midpoint_even_259
  simp only [tree259,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox259,candidate_valid h (FixedTape.midBox ibox259),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox259 106 (FixedTape.rowsAux denominator ibox259 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox259) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_259
private noncomputable def tree258 : TapeTree := .centered (candidateRows ibox258) (candidateRows (FixedTape.midBox ibox258))
attribute [irreducible] tree258
private theorem sign_258 : 2*denominator*(computed denominator (FixedTape.midBox ibox258)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox258).gradient k).lo.natAbs ((computed denominator ibox258).gradient k).hi.natAbs : Int)*((ibox258 k).hi-(ibox258 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox258
    (computed denominator ibox258) (computed denominator (FixedTape.midBox ibox258))
    (by decide +kernel)
private theorem midpoint_even_258 : ∀ k, 2 ∣ (ibox258 k).lo+(ibox258 k).hi := by decide +kernel
private theorem accepted_258 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox258) tree258 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox258 midpoint_even_258
  simp only [tree258,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox258,candidate_valid h (FixedTape.midBox ibox258),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox258 106 (FixedTape.rowsAux denominator ibox258 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox258) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_258
private noncomputable def tree257 : TapeTree := .split 2 (((418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree258 tree259
attribute [irreducible] tree257
private theorem accepted_257 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox257) tree257 = true := by
  simp only [tree257,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox257 2 (418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) false,decode_split denominator ibox257 2 (418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_258 h,accepted_259 h⟩
private noncomputable def tree256 : TapeTree := .centered (candidateRows ibox256) (candidateRows (FixedTape.midBox ibox256))
attribute [irreducible] tree256
private theorem sign_256 : 2*denominator*(computed denominator (FixedTape.midBox ibox256)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox256).gradient k).lo.natAbs ((computed denominator ibox256).gradient k).hi.natAbs : Int)*((ibox256 k).hi-(ibox256 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox256
    (computed denominator ibox256) (computed denominator (FixedTape.midBox ibox256))
    (by decide +kernel)
private theorem midpoint_even_256 : ∀ k, 2 ∣ (ibox256 k).lo+(ibox256 k).hi := by decide +kernel
private theorem accepted_256 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox256) tree256 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox256 midpoint_even_256
  simp only [tree256,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox256,candidate_valid h (FixedTape.midBox ibox256),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox256 106 (FixedTape.rowsAux denominator ibox256 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox256) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_256
private noncomputable def tree255 : TapeTree := .centered (candidateRows ibox255) (candidateRows (FixedTape.midBox ibox255))
attribute [irreducible] tree255
private theorem sign_255 : 2*denominator*(computed denominator (FixedTape.midBox ibox255)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox255).gradient k).lo.natAbs ((computed denominator ibox255).gradient k).hi.natAbs : Int)*((ibox255 k).hi-(ibox255 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox255
    (computed denominator ibox255) (computed denominator (FixedTape.midBox ibox255))
    (by decide +kernel)
private theorem midpoint_even_255 : ∀ k, 2 ∣ (ibox255 k).lo+(ibox255 k).hi := by decide +kernel
private theorem accepted_255 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox255) tree255 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox255 midpoint_even_255
  simp only [tree255,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox255,candidate_valid h (FixedTape.midBox ibox255),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox255 106 (FixedTape.rowsAux denominator ibox255 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox255) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_255
private noncomputable def tree254 : TapeTree := .split 2 (((418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree255 tree256
attribute [irreducible] tree254
private theorem accepted_254 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox254) tree254 = true := by
  simp only [tree254,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox254 2 (418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) false,decode_split denominator ibox254 2 (418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_255 h,accepted_256 h⟩
private noncomputable def tree253 : TapeTree := .centered (candidateRows ibox253) (candidateRows (FixedTape.midBox ibox253))
attribute [irreducible] tree253
private theorem sign_253 : 2*denominator*(computed denominator (FixedTape.midBox ibox253)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox253).gradient k).lo.natAbs ((computed denominator ibox253).gradient k).hi.natAbs : Int)*((ibox253 k).hi-(ibox253 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox253
    (computed denominator ibox253) (computed denominator (FixedTape.midBox ibox253))
    (by decide +kernel)
private theorem midpoint_even_253 : ∀ k, 2 ∣ (ibox253 k).lo+(ibox253 k).hi := by decide +kernel
private theorem accepted_253 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox253) tree253 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox253 midpoint_even_253
  simp only [tree253,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox253,candidate_valid h (FixedTape.midBox ibox253),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox253 106 (FixedTape.rowsAux denominator ibox253 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox253) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_253
private noncomputable def tree252 : TapeTree := .centered (candidateRows ibox252) (candidateRows (FixedTape.midBox ibox252))
attribute [irreducible] tree252
private theorem sign_252 : 2*denominator*(computed denominator (FixedTape.midBox ibox252)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox252).gradient k).lo.natAbs ((computed denominator ibox252).gradient k).hi.natAbs : Int)*((ibox252 k).hi-(ibox252 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox252
    (computed denominator ibox252) (computed denominator (FixedTape.midBox ibox252))
    (by decide +kernel)
private theorem midpoint_even_252 : ∀ k, 2 ∣ (ibox252 k).lo+(ibox252 k).hi := by decide +kernel
private theorem accepted_252 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox252) tree252 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox252 midpoint_even_252
  simp only [tree252,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox252,candidate_valid h (FixedTape.midBox ibox252),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox252 106 (FixedTape.rowsAux denominator ibox252 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox252) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_252
private noncomputable def tree251 : TapeTree := .split 2 (((418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree252 tree253
attribute [irreducible] tree251
private theorem accepted_251 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox251) tree251 = true := by
  simp only [tree251,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox251 2 (418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) false,decode_split denominator ibox251 2 (418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_252 h,accepted_253 h⟩
private noncomputable def tree250 : TapeTree := .split 3 (((380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree251 tree254
attribute [irreducible] tree250
private theorem accepted_250 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox250) tree250 = true := by
  simp only [tree250,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox250 3 (380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) false,decode_split denominator ibox250 3 (380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_251 h,accepted_254 h⟩
private noncomputable def tree249 : TapeTree := .split 3 (((456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree250 tree257
attribute [irreducible] tree249
private theorem accepted_249 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox249) tree249 = true := by
  simp only [tree249,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox249 3 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) false,decode_split denominator ibox249 3 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_250 h,accepted_257 h⟩
private noncomputable def tree248 : TapeTree := .centered (candidateRows ibox248) (candidateRows (FixedTape.midBox ibox248))
attribute [irreducible] tree248
private theorem sign_248 : 2*denominator*(computed denominator (FixedTape.midBox ibox248)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox248).gradient k).lo.natAbs ((computed denominator ibox248).gradient k).hi.natAbs : Int)*((ibox248 k).hi-(ibox248 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox248
    (computed denominator ibox248) (computed denominator (FixedTape.midBox ibox248))
    (by decide +kernel)
private theorem midpoint_even_248 : ∀ k, 2 ∣ (ibox248 k).lo+(ibox248 k).hi := by decide +kernel
private theorem accepted_248 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox248) tree248 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox248 midpoint_even_248
  simp only [tree248,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox248,candidate_valid h (FixedTape.midBox ibox248),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox248 106 (FixedTape.rowsAux denominator ibox248 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox248) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_248
private noncomputable def tree247 : TapeTree := .centered (candidateRows ibox247) (candidateRows (FixedTape.midBox ibox247))
attribute [irreducible] tree247
private theorem sign_247 : 2*denominator*(computed denominator (FixedTape.midBox ibox247)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox247).gradient k).lo.natAbs ((computed denominator ibox247).gradient k).hi.natAbs : Int)*((ibox247 k).hi-(ibox247 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox247
    (computed denominator ibox247) (computed denominator (FixedTape.midBox ibox247))
    (by decide +kernel)
private theorem midpoint_even_247 : ∀ k, 2 ∣ (ibox247 k).lo+(ibox247 k).hi := by decide +kernel
private theorem accepted_247 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox247) tree247 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox247 midpoint_even_247
  simp only [tree247,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox247,candidate_valid h (FixedTape.midBox ibox247),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox247 106 (FixedTape.rowsAux denominator ibox247 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox247) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_247
private noncomputable def tree246 : TapeTree := .split 2 (((342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree247 tree248
attribute [irreducible] tree246
private theorem accepted_246 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox246) tree246 = true := by
  simp only [tree246,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox246 2 (342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 : Int) false,decode_split denominator ibox246 2 (342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_247 h,accepted_248 h⟩
private noncomputable def tree245 : TapeTree := .centered (candidateRows ibox245) (candidateRows (FixedTape.midBox ibox245))
attribute [irreducible] tree245
private theorem sign_245 : 2*denominator*(computed denominator (FixedTape.midBox ibox245)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox245).gradient k).lo.natAbs ((computed denominator ibox245).gradient k).hi.natAbs : Int)*((ibox245 k).hi-(ibox245 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox245
    (computed denominator ibox245) (computed denominator (FixedTape.midBox ibox245))
    (by decide +kernel)
private theorem midpoint_even_245 : ∀ k, 2 ∣ (ibox245 k).lo+(ibox245 k).hi := by decide +kernel
private theorem accepted_245 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox245) tree245 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox245 midpoint_even_245
  simp only [tree245,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox245,candidate_valid h (FixedTape.midBox ibox245),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox245 106 (FixedTape.rowsAux denominator ibox245 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox245) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_245
private noncomputable def tree244 : TapeTree := .centered (candidateRows ibox244) (candidateRows (FixedTape.midBox ibox244))
attribute [irreducible] tree244
private theorem sign_244 : 2*denominator*(computed denominator (FixedTape.midBox ibox244)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox244).gradient k).lo.natAbs ((computed denominator ibox244).gradient k).hi.natAbs : Int)*((ibox244 k).hi-(ibox244 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox244
    (computed denominator ibox244) (computed denominator (FixedTape.midBox ibox244))
    (by decide +kernel)
private theorem midpoint_even_244 : ∀ k, 2 ∣ (ibox244 k).lo+(ibox244 k).hi := by decide +kernel
private theorem accepted_244 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox244) tree244 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox244 midpoint_even_244
  simp only [tree244,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox244,candidate_valid h (FixedTape.midBox ibox244),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox244 106 (FixedTape.rowsAux denominator ibox244 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox244) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_244
private noncomputable def tree243 : TapeTree := .split 3 (((380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree244 tree245
attribute [irreducible] tree243
private theorem accepted_243 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox243) tree243 = true := by
  simp only [tree243,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox243 3 (380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) false,decode_split denominator ibox243 3 (380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_244 h,accepted_245 h⟩
private noncomputable def tree242 : TapeTree := .centered (candidateRows ibox242) (candidateRows (FixedTape.midBox ibox242))
attribute [irreducible] tree242
private theorem sign_242 : 2*denominator*(computed denominator (FixedTape.midBox ibox242)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox242).gradient k).lo.natAbs ((computed denominator ibox242).gradient k).hi.natAbs : Int)*((ibox242 k).hi-(ibox242 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox242
    (computed denominator ibox242) (computed denominator (FixedTape.midBox ibox242))
    (by decide +kernel)
private theorem midpoint_even_242 : ∀ k, 2 ∣ (ibox242 k).lo+(ibox242 k).hi := by decide +kernel
private theorem accepted_242 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox242) tree242 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox242 midpoint_even_242
  simp only [tree242,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox242,candidate_valid h (FixedTape.midBox ibox242),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox242 106 (FixedTape.rowsAux denominator ibox242 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox242) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_242
private noncomputable def tree241 : TapeTree := .centered (candidateRows ibox241) (candidateRows (FixedTape.midBox ibox241))
attribute [irreducible] tree241
private theorem sign_241 : 2*denominator*(computed denominator (FixedTape.midBox ibox241)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox241).gradient k).lo.natAbs ((computed denominator ibox241).gradient k).hi.natAbs : Int)*((ibox241 k).hi-(ibox241 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox241
    (computed denominator ibox241) (computed denominator (FixedTape.midBox ibox241))
    (by decide +kernel)
private theorem midpoint_even_241 : ∀ k, 2 ∣ (ibox241 k).lo+(ibox241 k).hi := by decide +kernel
private theorem accepted_241 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox241) tree241 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox241 midpoint_even_241
  simp only [tree241,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox241,candidate_valid h (FixedTape.midBox ibox241),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox241 106 (FixedTape.rowsAux denominator ibox241 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox241) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_241
private noncomputable def tree240 : TapeTree := .split 3 (((380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree241 tree242
attribute [irreducible] tree240
private theorem accepted_240 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox240) tree240 = true := by
  simp only [tree240,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox240 3 (380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) false,decode_split denominator ibox240 3 (380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_241 h,accepted_242 h⟩
private noncomputable def tree239 : TapeTree := .split 2 (((342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree240 tree243
attribute [irreducible] tree239
private theorem accepted_239 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox239) tree239 = true := by
  simp only [tree239,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox239 2 (342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 : Int) false,decode_split denominator ibox239 2 (342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_240 h,accepted_243 h⟩
private noncomputable def tree238 : TapeTree := .split 3 (((456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree239 tree246
attribute [irreducible] tree238
private theorem accepted_238 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox238) tree238 = true := by
  simp only [tree238,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox238 3 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) false,decode_split denominator ibox238 3 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_239 h,accepted_246 h⟩
private noncomputable def tree237 : TapeTree := .split 2 (((380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree238 tree249
attribute [irreducible] tree237
private theorem accepted_237 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox237) tree237 = true := by
  simp only [tree237,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox237 2 (380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) false,decode_split denominator ibox237 2 (380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_238 h,accepted_249 h⟩
private noncomputable def tree236 : TapeTree := .split 2 (((456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree237 tree260
attribute [irreducible] tree236
private theorem accepted_236 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox236) tree236 = true := by
  simp only [tree236,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox236 2 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) false,decode_split denominator ibox236 2 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_237 h,accepted_260 h⟩
private noncomputable def tree235 : TapeTree := .centered (candidateRows ibox235) (candidateRows (FixedTape.midBox ibox235))
attribute [irreducible] tree235
private theorem sign_235 : 2*denominator*(computed denominator (FixedTape.midBox ibox235)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox235).gradient k).lo.natAbs ((computed denominator ibox235).gradient k).hi.natAbs : Int)*((ibox235 k).hi-(ibox235 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox235
    (computed denominator ibox235) (computed denominator (FixedTape.midBox ibox235))
    (by decide +kernel)
private theorem midpoint_even_235 : ∀ k, 2 ∣ (ibox235 k).lo+(ibox235 k).hi := by decide +kernel
private theorem accepted_235 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox235) tree235 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox235 midpoint_even_235
  simp only [tree235,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox235,candidate_valid h (FixedTape.midBox ibox235),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox235 106 (FixedTape.rowsAux denominator ibox235 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox235) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_235
private noncomputable def tree234 : TapeTree := .centered (candidateRows ibox234) (candidateRows (FixedTape.midBox ibox234))
attribute [irreducible] tree234
private theorem sign_234 : 2*denominator*(computed denominator (FixedTape.midBox ibox234)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox234).gradient k).lo.natAbs ((computed denominator ibox234).gradient k).hi.natAbs : Int)*((ibox234 k).hi-(ibox234 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox234
    (computed denominator ibox234) (computed denominator (FixedTape.midBox ibox234))
    (by decide +kernel)
private theorem midpoint_even_234 : ∀ k, 2 ∣ (ibox234 k).lo+(ibox234 k).hi := by decide +kernel
private theorem accepted_234 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox234) tree234 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox234 midpoint_even_234
  simp only [tree234,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox234,candidate_valid h (FixedTape.midBox ibox234),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox234 106 (FixedTape.rowsAux denominator ibox234 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox234) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_234
private noncomputable def tree233 : TapeTree := .split 2 (((571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree234 tree235
attribute [irreducible] tree233
private theorem accepted_233 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox233) tree233 = true := by
  simp only [tree233,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox233 2 (571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) false,decode_split denominator ibox233 2 (571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_234 h,accepted_235 h⟩
private noncomputable def tree232 : TapeTree := .centered (candidateRows ibox232) (candidateRows (FixedTape.midBox ibox232))
attribute [irreducible] tree232
private theorem sign_232 : 2*denominator*(computed denominator (FixedTape.midBox ibox232)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox232).gradient k).lo.natAbs ((computed denominator ibox232).gradient k).hi.natAbs : Int)*((ibox232 k).hi-(ibox232 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox232
    (computed denominator ibox232) (computed denominator (FixedTape.midBox ibox232))
    (by decide +kernel)
private theorem midpoint_even_232 : ∀ k, 2 ∣ (ibox232 k).lo+(ibox232 k).hi := by decide +kernel
private theorem accepted_232 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox232) tree232 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox232 midpoint_even_232
  simp only [tree232,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox232,candidate_valid h (FixedTape.midBox ibox232),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox232 106 (FixedTape.rowsAux denominator ibox232 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox232) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_232
private noncomputable def tree231 : TapeTree := .centered (candidateRows ibox231) (candidateRows (FixedTape.midBox ibox231))
attribute [irreducible] tree231
private theorem sign_231 : 2*denominator*(computed denominator (FixedTape.midBox ibox231)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox231).gradient k).lo.natAbs ((computed denominator ibox231).gradient k).hi.natAbs : Int)*((ibox231 k).hi-(ibox231 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox231
    (computed denominator ibox231) (computed denominator (FixedTape.midBox ibox231))
    (by decide +kernel)
private theorem midpoint_even_231 : ∀ k, 2 ∣ (ibox231 k).lo+(ibox231 k).hi := by decide +kernel
private theorem accepted_231 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox231) tree231 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox231 midpoint_even_231
  simp only [tree231,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox231,candidate_valid h (FixedTape.midBox ibox231),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox231 106 (FixedTape.rowsAux denominator ibox231 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox231) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_231
private noncomputable def tree230 : TapeTree := .split 3 (((190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree231 tree232
attribute [irreducible] tree230
private theorem accepted_230 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox230) tree230 = true := by
  simp only [tree230,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox230 3 (190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) false,decode_split denominator ibox230 3 (190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_231 h,accepted_232 h⟩
private noncomputable def tree229 : TapeTree := .centered (candidateRows ibox229) (candidateRows (FixedTape.midBox ibox229))
attribute [irreducible] tree229
private theorem sign_229 : 2*denominator*(computed denominator (FixedTape.midBox ibox229)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox229).gradient k).lo.natAbs ((computed denominator ibox229).gradient k).hi.natAbs : Int)*((ibox229 k).hi-(ibox229 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox229
    (computed denominator ibox229) (computed denominator (FixedTape.midBox ibox229))
    (by decide +kernel)
private theorem midpoint_even_229 : ∀ k, 2 ∣ (ibox229 k).lo+(ibox229 k).hi := by decide +kernel
private theorem accepted_229 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox229) tree229 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox229 midpoint_even_229
  simp only [tree229,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox229,candidate_valid h (FixedTape.midBox ibox229),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox229 106 (FixedTape.rowsAux denominator ibox229 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox229) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_229
private noncomputable def tree228 : TapeTree := .centered (candidateRows ibox228) (candidateRows (FixedTape.midBox ibox228))
attribute [irreducible] tree228
private theorem sign_228 : 2*denominator*(computed denominator (FixedTape.midBox ibox228)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox228).gradient k).lo.natAbs ((computed denominator ibox228).gradient k).hi.natAbs : Int)*((ibox228 k).hi-(ibox228 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox228
    (computed denominator ibox228) (computed denominator (FixedTape.midBox ibox228))
    (by decide +kernel)
private theorem midpoint_even_228 : ∀ k, 2 ∣ (ibox228 k).lo+(ibox228 k).hi := by decide +kernel
private theorem accepted_228 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox228) tree228 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox228 midpoint_even_228
  simp only [tree228,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox228,candidate_valid h (FixedTape.midBox ibox228),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox228 106 (FixedTape.rowsAux denominator ibox228 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox228) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_228
private noncomputable def tree227 : TapeTree := .split 3 (((190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree228 tree229
attribute [irreducible] tree227
private theorem accepted_227 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox227) tree227 = true := by
  simp only [tree227,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox227 3 (190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) false,decode_split denominator ibox227 3 (190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_228 h,accepted_229 h⟩
private noncomputable def tree226 : TapeTree := .split 2 (((571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree227 tree230
attribute [irreducible] tree226
private theorem accepted_226 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox226) tree226 = true := by
  simp only [tree226,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox226 2 (571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) false,decode_split denominator ibox226 2 (571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_227 h,accepted_230 h⟩
private noncomputable def tree225 : TapeTree := .split 3 (((228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree226 tree233
attribute [irreducible] tree225
private theorem accepted_225 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox225) tree225 = true := by
  simp only [tree225,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox225 3 (228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) false,decode_split denominator ibox225 3 (228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_226 h,accepted_233 h⟩
private noncomputable def tree224 : TapeTree := .centered (candidateRows ibox224) (candidateRows (FixedTape.midBox ibox224))
attribute [irreducible] tree224
private theorem sign_224 : 2*denominator*(computed denominator (FixedTape.midBox ibox224)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox224).gradient k).lo.natAbs ((computed denominator ibox224).gradient k).hi.natAbs : Int)*((ibox224 k).hi-(ibox224 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox224
    (computed denominator ibox224) (computed denominator (FixedTape.midBox ibox224))
    (by decide +kernel)
private theorem midpoint_even_224 : ∀ k, 2 ∣ (ibox224 k).lo+(ibox224 k).hi := by decide +kernel
private theorem accepted_224 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox224) tree224 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox224 midpoint_even_224
  simp only [tree224,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox224,candidate_valid h (FixedTape.midBox ibox224),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox224 106 (FixedTape.rowsAux denominator ibox224 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox224) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_224
private noncomputable def tree223 : TapeTree := .centered (candidateRows ibox223) (candidateRows (FixedTape.midBox ibox223))
attribute [irreducible] tree223
private theorem sign_223 : 2*denominator*(computed denominator (FixedTape.midBox ibox223)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox223).gradient k).lo.natAbs ((computed denominator ibox223).gradient k).hi.natAbs : Int)*((ibox223 k).hi-(ibox223 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox223
    (computed denominator ibox223) (computed denominator (FixedTape.midBox ibox223))
    (by decide +kernel)
private theorem midpoint_even_223 : ∀ k, 2 ∣ (ibox223 k).lo+(ibox223 k).hi := by decide +kernel
private theorem accepted_223 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox223) tree223 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox223 midpoint_even_223
  simp only [tree223,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox223,candidate_valid h (FixedTape.midBox ibox223),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox223 106 (FixedTape.rowsAux denominator ibox223 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox223) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_223
private noncomputable def tree222 : TapeTree := .split 2 (((495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree223 tree224
attribute [irreducible] tree222
private theorem accepted_222 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox222) tree222 = true := by
  simp only [tree222,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox222 2 (495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) false,decode_split denominator ibox222 2 (495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_223 h,accepted_224 h⟩
private noncomputable def tree221 : TapeTree := .centered (candidateRows ibox221) (candidateRows (FixedTape.midBox ibox221))
attribute [irreducible] tree221
private theorem sign_221 : 2*denominator*(computed denominator (FixedTape.midBox ibox221)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox221).gradient k).lo.natAbs ((computed denominator ibox221).gradient k).hi.natAbs : Int)*((ibox221 k).hi-(ibox221 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox221
    (computed denominator ibox221) (computed denominator (FixedTape.midBox ibox221))
    (by decide +kernel)
private theorem midpoint_even_221 : ∀ k, 2 ∣ (ibox221 k).lo+(ibox221 k).hi := by decide +kernel
private theorem accepted_221 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox221) tree221 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox221 midpoint_even_221
  simp only [tree221,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox221,candidate_valid h (FixedTape.midBox ibox221),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox221 106 (FixedTape.rowsAux denominator ibox221 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox221) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_221
private noncomputable def tree220 : TapeTree := .centered (candidateRows ibox220) (candidateRows (FixedTape.midBox ibox220))
attribute [irreducible] tree220
private theorem sign_220 : 2*denominator*(computed denominator (FixedTape.midBox ibox220)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox220).gradient k).lo.natAbs ((computed denominator ibox220).gradient k).hi.natAbs : Int)*((ibox220 k).hi-(ibox220 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox220
    (computed denominator ibox220) (computed denominator (FixedTape.midBox ibox220))
    (by decide +kernel)
private theorem midpoint_even_220 : ∀ k, 2 ∣ (ibox220 k).lo+(ibox220 k).hi := by decide +kernel
private theorem accepted_220 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox220) tree220 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox220 midpoint_even_220
  simp only [tree220,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox220,candidate_valid h (FixedTape.midBox ibox220),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox220 106 (FixedTape.rowsAux denominator ibox220 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox220) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_220
private noncomputable def tree219 : TapeTree := .split 3 (((190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree220 tree221
attribute [irreducible] tree219
private theorem accepted_219 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox219) tree219 = true := by
  simp only [tree219,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox219 3 (190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) false,decode_split denominator ibox219 3 (190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_220 h,accepted_221 h⟩
private noncomputable def tree218 : TapeTree := .centered (candidateRows ibox218) (candidateRows (FixedTape.midBox ibox218))
attribute [irreducible] tree218
private theorem sign_218 : 2*denominator*(computed denominator (FixedTape.midBox ibox218)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox218).gradient k).lo.natAbs ((computed denominator ibox218).gradient k).hi.natAbs : Int)*((ibox218 k).hi-(ibox218 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox218
    (computed denominator ibox218) (computed denominator (FixedTape.midBox ibox218))
    (by decide +kernel)
private theorem midpoint_even_218 : ∀ k, 2 ∣ (ibox218 k).lo+(ibox218 k).hi := by decide +kernel
private theorem accepted_218 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox218) tree218 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox218 midpoint_even_218
  simp only [tree218,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox218,candidate_valid h (FixedTape.midBox ibox218),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox218 106 (FixedTape.rowsAux denominator ibox218 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox218) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_218
private noncomputable def tree217 : TapeTree := .centered (candidateRows ibox217) (candidateRows (FixedTape.midBox ibox217))
attribute [irreducible] tree217
private theorem sign_217 : 2*denominator*(computed denominator (FixedTape.midBox ibox217)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox217).gradient k).lo.natAbs ((computed denominator ibox217).gradient k).hi.natAbs : Int)*((ibox217 k).hi-(ibox217 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox217
    (computed denominator ibox217) (computed denominator (FixedTape.midBox ibox217))
    (by decide +kernel)
private theorem midpoint_even_217 : ∀ k, 2 ∣ (ibox217 k).lo+(ibox217 k).hi := by decide +kernel
private theorem accepted_217 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox217) tree217 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox217 midpoint_even_217
  simp only [tree217,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox217,candidate_valid h (FixedTape.midBox ibox217),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox217 106 (FixedTape.rowsAux denominator ibox217 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox217) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_217
private noncomputable def tree216 : TapeTree := .split 3 (((190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree217 tree218
attribute [irreducible] tree216
private theorem accepted_216 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox216) tree216 = true := by
  simp only [tree216,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox216 3 (190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) false,decode_split denominator ibox216 3 (190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_217 h,accepted_218 h⟩
private noncomputable def tree215 : TapeTree := .split 2 (((495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree216 tree219
attribute [irreducible] tree215
private theorem accepted_215 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox215) tree215 = true := by
  simp only [tree215,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox215 2 (495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) false,decode_split denominator ibox215 2 (495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_216 h,accepted_219 h⟩
private noncomputable def tree214 : TapeTree := .split 3 (((228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree215 tree222
attribute [irreducible] tree214
private theorem accepted_214 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox214) tree214 = true := by
  simp only [tree214,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox214 3 (228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) false,decode_split denominator ibox214 3 (228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_215 h,accepted_222 h⟩
private noncomputable def tree213 : TapeTree := .split 2 (((533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree214 tree225
attribute [irreducible] tree213
private theorem accepted_213 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox213) tree213 = true := by
  simp only [tree213,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox213 2 (533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 : Int) false,decode_split denominator ibox213 2 (533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_214 h,accepted_225 h⟩
private noncomputable def tree212 : TapeTree := .centered (candidateRows ibox212) (candidateRows (FixedTape.midBox ibox212))
attribute [irreducible] tree212
private theorem sign_212 : 2*denominator*(computed denominator (FixedTape.midBox ibox212)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox212).gradient k).lo.natAbs ((computed denominator ibox212).gradient k).hi.natAbs : Int)*((ibox212 k).hi-(ibox212 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox212
    (computed denominator ibox212) (computed denominator (FixedTape.midBox ibox212))
    (by decide +kernel)
private theorem midpoint_even_212 : ∀ k, 2 ∣ (ibox212 k).lo+(ibox212 k).hi := by decide +kernel
private theorem accepted_212 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox212) tree212 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox212 midpoint_even_212
  simp only [tree212,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox212,candidate_valid h (FixedTape.midBox ibox212),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox212 106 (FixedTape.rowsAux denominator ibox212 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox212) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_212
private noncomputable def tree211 : TapeTree := .centered (candidateRows ibox211) (candidateRows (FixedTape.midBox ibox211))
attribute [irreducible] tree211
private theorem sign_211 : 2*denominator*(computed denominator (FixedTape.midBox ibox211)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox211).gradient k).lo.natAbs ((computed denominator ibox211).gradient k).hi.natAbs : Int)*((ibox211 k).hi-(ibox211 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox211
    (computed denominator ibox211) (computed denominator (FixedTape.midBox ibox211))
    (by decide +kernel)
private theorem midpoint_even_211 : ∀ k, 2 ∣ (ibox211 k).lo+(ibox211 k).hi := by decide +kernel
private theorem accepted_211 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox211) tree211 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox211 midpoint_even_211
  simp only [tree211,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox211,candidate_valid h (FixedTape.midBox ibox211),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox211 106 (FixedTape.rowsAux denominator ibox211 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox211) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_211
private noncomputable def tree210 : TapeTree := .split 3 (((114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree211 tree212
attribute [irreducible] tree210
private theorem accepted_210 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox210) tree210 = true := by
  simp only [tree210,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox210 3 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) false,decode_split denominator ibox210 3 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_211 h,accepted_212 h⟩
private noncomputable def tree209 : TapeTree := .centered (candidateRows ibox209) (candidateRows (FixedTape.midBox ibox209))
attribute [irreducible] tree209
private theorem sign_209 : 2*denominator*(computed denominator (FixedTape.midBox ibox209)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox209).gradient k).lo.natAbs ((computed denominator ibox209).gradient k).hi.natAbs : Int)*((ibox209 k).hi-(ibox209 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox209
    (computed denominator ibox209) (computed denominator (FixedTape.midBox ibox209))
    (by decide +kernel)
private theorem midpoint_even_209 : ∀ k, 2 ∣ (ibox209 k).lo+(ibox209 k).hi := by decide +kernel
private theorem accepted_209 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox209) tree209 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox209 midpoint_even_209
  simp only [tree209,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox209,candidate_valid h (FixedTape.midBox ibox209),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox209 106 (FixedTape.rowsAux denominator ibox209 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox209) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_209
private noncomputable def tree208 : TapeTree := .centered (candidateRows ibox208) (candidateRows (FixedTape.midBox ibox208))
attribute [irreducible] tree208
private theorem sign_208 : 2*denominator*(computed denominator (FixedTape.midBox ibox208)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox208).gradient k).lo.natAbs ((computed denominator ibox208).gradient k).hi.natAbs : Int)*((ibox208 k).hi-(ibox208 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox208
    (computed denominator ibox208) (computed denominator (FixedTape.midBox ibox208))
    (by decide +kernel)
private theorem midpoint_even_208 : ∀ k, 2 ∣ (ibox208 k).lo+(ibox208 k).hi := by decide +kernel
private theorem accepted_208 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox208) tree208 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox208 midpoint_even_208
  simp only [tree208,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox208,candidate_valid h (FixedTape.midBox ibox208),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox208 106 (FixedTape.rowsAux denominator ibox208 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox208) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_208
private noncomputable def tree207 : TapeTree := .split 3 (((114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree208 tree209
attribute [irreducible] tree207
private theorem accepted_207 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox207) tree207 = true := by
  simp only [tree207,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox207 3 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) false,decode_split denominator ibox207 3 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_208 h,accepted_209 h⟩
private noncomputable def tree206 : TapeTree := .split 2 (((571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree207 tree210
attribute [irreducible] tree206
private theorem accepted_206 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox206) tree206 = true := by
  simp only [tree206,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox206 2 (571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) false,decode_split denominator ibox206 2 (571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_207 h,accepted_210 h⟩
private noncomputable def tree205 : TapeTree := .centered (candidateRows ibox205) (candidateRows (FixedTape.midBox ibox205))
attribute [irreducible] tree205
private theorem sign_205 : 2*denominator*(computed denominator (FixedTape.midBox ibox205)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox205).gradient k).lo.natAbs ((computed denominator ibox205).gradient k).hi.natAbs : Int)*((ibox205 k).hi-(ibox205 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox205
    (computed denominator ibox205) (computed denominator (FixedTape.midBox ibox205))
    (by decide +kernel)
private theorem midpoint_even_205 : ∀ k, 2 ∣ (ibox205 k).lo+(ibox205 k).hi := by decide +kernel
private theorem accepted_205 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox205) tree205 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox205 midpoint_even_205
  simp only [tree205,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox205,candidate_valid h (FixedTape.midBox ibox205),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox205 106 (FixedTape.rowsAux denominator ibox205 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox205) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_205
private noncomputable def tree204 : TapeTree := .centered (candidateRows ibox204) (candidateRows (FixedTape.midBox ibox204))
attribute [irreducible] tree204
private theorem sign_204 : 2*denominator*(computed denominator (FixedTape.midBox ibox204)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox204).gradient k).lo.natAbs ((computed denominator ibox204).gradient k).hi.natAbs : Int)*((ibox204 k).hi-(ibox204 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox204
    (computed denominator ibox204) (computed denominator (FixedTape.midBox ibox204))
    (by decide +kernel)
private theorem midpoint_even_204 : ∀ k, 2 ∣ (ibox204 k).lo+(ibox204 k).hi := by decide +kernel
private theorem accepted_204 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox204) tree204 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox204 midpoint_even_204
  simp only [tree204,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox204,candidate_valid h (FixedTape.midBox ibox204),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox204 106 (FixedTape.rowsAux denominator ibox204 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox204) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_204
private noncomputable def tree203 : TapeTree := .split 0 (((307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) : ℚ)/(denominator : ℚ)) tree204 tree205
attribute [irreducible] tree203
private theorem accepted_203 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox203) tree203 = true := by
  simp only [tree203,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox203 0 (307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) false,decode_split denominator ibox203 0 (307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_204 h,accepted_205 h⟩
private noncomputable def tree202 : TapeTree := .centered (candidateRows ibox202) (candidateRows (FixedTape.midBox ibox202))
attribute [irreducible] tree202
private theorem sign_202 : 2*denominator*(computed denominator (FixedTape.midBox ibox202)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox202).gradient k).lo.natAbs ((computed denominator ibox202).gradient k).hi.natAbs : Int)*((ibox202 k).hi-(ibox202 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox202
    (computed denominator ibox202) (computed denominator (FixedTape.midBox ibox202))
    (by decide +kernel)
private theorem midpoint_even_202 : ∀ k, 2 ∣ (ibox202 k).lo+(ibox202 k).hi := by decide +kernel
private theorem accepted_202 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox202) tree202 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox202 midpoint_even_202
  simp only [tree202,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox202,candidate_valid h (FixedTape.midBox ibox202),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox202 106 (FixedTape.rowsAux denominator ibox202 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox202) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_202
private noncomputable def tree201 : TapeTree := .centered (candidateRows ibox201) (candidateRows (FixedTape.midBox ibox201))
attribute [irreducible] tree201
private theorem sign_201 : 2*denominator*(computed denominator (FixedTape.midBox ibox201)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox201).gradient k).lo.natAbs ((computed denominator ibox201).gradient k).hi.natAbs : Int)*((ibox201 k).hi-(ibox201 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox201
    (computed denominator ibox201) (computed denominator (FixedTape.midBox ibox201))
    (by decide +kernel)
private theorem midpoint_even_201 : ∀ k, 2 ∣ (ibox201 k).lo+(ibox201 k).hi := by decide +kernel
private theorem accepted_201 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox201) tree201 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox201 midpoint_even_201
  simp only [tree201,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox201,candidate_valid h (FixedTape.midBox ibox201),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox201 106 (FixedTape.rowsAux denominator ibox201 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox201) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_201
private noncomputable def tree200 : TapeTree := .split 0 (((307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) : ℚ)/(denominator : ℚ)) tree201 tree202
attribute [irreducible] tree200
private theorem accepted_200 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox200) tree200 = true := by
  simp only [tree200,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox200 0 (307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) false,decode_split denominator ibox200 0 (307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_201 h,accepted_202 h⟩
private noncomputable def tree199 : TapeTree := .split 3 (((38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree200 tree203
attribute [irreducible] tree199
private theorem accepted_199 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox199) tree199 = true := by
  simp only [tree199,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox199 3 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) false,decode_split denominator ibox199 3 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_200 h,accepted_203 h⟩
private noncomputable def tree198 : TapeTree := .centered (candidateRows ibox198) (candidateRows (FixedTape.midBox ibox198))
attribute [irreducible] tree198
private theorem sign_198 : 2*denominator*(computed denominator (FixedTape.midBox ibox198)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox198).gradient k).lo.natAbs ((computed denominator ibox198).gradient k).hi.natAbs : Int)*((ibox198 k).hi-(ibox198 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox198
    (computed denominator ibox198) (computed denominator (FixedTape.midBox ibox198))
    (by decide +kernel)
private theorem midpoint_even_198 : ∀ k, 2 ∣ (ibox198 k).lo+(ibox198 k).hi := by decide +kernel
private theorem accepted_198 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox198) tree198 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox198 midpoint_even_198
  simp only [tree198,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox198,candidate_valid h (FixedTape.midBox ibox198),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox198 106 (FixedTape.rowsAux denominator ibox198 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox198) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_198
private noncomputable def tree197 : TapeTree := .centered (candidateRows ibox197) (candidateRows (FixedTape.midBox ibox197))
attribute [irreducible] tree197
private theorem sign_197 : 2*denominator*(computed denominator (FixedTape.midBox ibox197)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox197).gradient k).lo.natAbs ((computed denominator ibox197).gradient k).hi.natAbs : Int)*((ibox197 k).hi-(ibox197 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox197
    (computed denominator ibox197) (computed denominator (FixedTape.midBox ibox197))
    (by decide +kernel)
private theorem midpoint_even_197 : ∀ k, 2 ∣ (ibox197 k).lo+(ibox197 k).hi := by decide +kernel
private theorem accepted_197 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox197) tree197 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox197 midpoint_even_197
  simp only [tree197,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox197,candidate_valid h (FixedTape.midBox ibox197),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox197 106 (FixedTape.rowsAux denominator ibox197 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox197) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_197
private noncomputable def tree196 : TapeTree := .split 0 (((307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) : ℚ)/(denominator : ℚ)) tree197 tree198
attribute [irreducible] tree196
private theorem accepted_196 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox196) tree196 = true := by
  simp only [tree196,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox196 0 (307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) false,decode_split denominator ibox196 0 (307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_197 h,accepted_198 h⟩
private noncomputable def tree195 : TapeTree := .centered (candidateRows ibox195) (candidateRows (FixedTape.midBox ibox195))
attribute [irreducible] tree195
private theorem sign_195 : 2*denominator*(computed denominator (FixedTape.midBox ibox195)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox195).gradient k).lo.natAbs ((computed denominator ibox195).gradient k).hi.natAbs : Int)*((ibox195 k).hi-(ibox195 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox195
    (computed denominator ibox195) (computed denominator (FixedTape.midBox ibox195))
    (by decide +kernel)
private theorem midpoint_even_195 : ∀ k, 2 ∣ (ibox195 k).lo+(ibox195 k).hi := by decide +kernel
private theorem accepted_195 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox195) tree195 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox195 midpoint_even_195
  simp only [tree195,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox195,candidate_valid h (FixedTape.midBox ibox195),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox195 106 (FixedTape.rowsAux denominator ibox195 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox195) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_195
private noncomputable def tree194 : TapeTree := .centered (candidateRows ibox194) (candidateRows (FixedTape.midBox ibox194))
attribute [irreducible] tree194
private theorem sign_194 : 2*denominator*(computed denominator (FixedTape.midBox ibox194)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox194).gradient k).lo.natAbs ((computed denominator ibox194).gradient k).hi.natAbs : Int)*((ibox194 k).hi-(ibox194 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox194
    (computed denominator ibox194) (computed denominator (FixedTape.midBox ibox194))
    (by decide +kernel)
private theorem midpoint_even_194 : ∀ k, 2 ∣ (ibox194 k).lo+(ibox194 k).hi := by decide +kernel
private theorem accepted_194 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox194) tree194 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox194 midpoint_even_194
  simp only [tree194,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox194,candidate_valid h (FixedTape.midBox ibox194),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox194 106 (FixedTape.rowsAux denominator ibox194 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox194) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_194
private noncomputable def tree193 : TapeTree := .split 0 (((307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) : ℚ)/(denominator : ℚ)) tree194 tree195
attribute [irreducible] tree193
private theorem accepted_193 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox193) tree193 = true := by
  simp only [tree193,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox193 0 (307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) false,decode_split denominator ibox193 0 (307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_194 h,accepted_195 h⟩
private noncomputable def tree192 : TapeTree := .split 3 (((38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree193 tree196
attribute [irreducible] tree192
private theorem accepted_192 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox192) tree192 = true := by
  simp only [tree192,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox192 3 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) false,decode_split denominator ibox192 3 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_193 h,accepted_196 h⟩
private noncomputable def tree191 : TapeTree := .split 2 (((571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree192 tree199
attribute [irreducible] tree191
private theorem accepted_191 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox191) tree191 = true := by
  simp only [tree191,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox191 2 (571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) false,decode_split denominator ibox191 2 (571170662805268230019472502656585443888694142759507448647598889933426523971606107819274649206784000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_192 h,accepted_199 h⟩
private noncomputable def tree190 : TapeTree := .split 3 (((76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree191 tree206
attribute [irreducible] tree190
private theorem accepted_190 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox190) tree190 = true := by
  simp only [tree190,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox190 3 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) false,decode_split denominator ibox190 3 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_191 h,accepted_206 h⟩
private noncomputable def tree189 : TapeTree := .centered (candidateRows ibox189) (candidateRows (FixedTape.midBox ibox189))
attribute [irreducible] tree189
private theorem sign_189 : 2*denominator*(computed denominator (FixedTape.midBox ibox189)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox189).gradient k).lo.natAbs ((computed denominator ibox189).gradient k).hi.natAbs : Int)*((ibox189 k).hi-(ibox189 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox189
    (computed denominator ibox189) (computed denominator (FixedTape.midBox ibox189))
    (by decide +kernel)
private theorem midpoint_even_189 : ∀ k, 2 ∣ (ibox189 k).lo+(ibox189 k).hi := by decide +kernel
private theorem accepted_189 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox189) tree189 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox189 midpoint_even_189
  simp only [tree189,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox189,candidate_valid h (FixedTape.midBox ibox189),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox189 106 (FixedTape.rowsAux denominator ibox189 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox189) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_189
private noncomputable def tree188 : TapeTree := .centered (candidateRows ibox188) (candidateRows (FixedTape.midBox ibox188))
attribute [irreducible] tree188
private theorem sign_188 : 2*denominator*(computed denominator (FixedTape.midBox ibox188)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox188).gradient k).lo.natAbs ((computed denominator ibox188).gradient k).hi.natAbs : Int)*((ibox188 k).hi-(ibox188 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox188
    (computed denominator ibox188) (computed denominator (FixedTape.midBox ibox188))
    (by decide +kernel)
private theorem midpoint_even_188 : ∀ k, 2 ∣ (ibox188 k).lo+(ibox188 k).hi := by decide +kernel
private theorem accepted_188 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox188) tree188 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox188 midpoint_even_188
  simp only [tree188,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox188,candidate_valid h (FixedTape.midBox ibox188),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox188 106 (FixedTape.rowsAux denominator ibox188 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox188) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_188
private noncomputable def tree187 : TapeTree := .split 3 (((114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree188 tree189
attribute [irreducible] tree187
private theorem accepted_187 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox187) tree187 = true := by
  simp only [tree187,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox187 3 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) false,decode_split denominator ibox187 3 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_188 h,accepted_189 h⟩
private noncomputable def tree186 : TapeTree := .centered (candidateRows ibox186) (candidateRows (FixedTape.midBox ibox186))
attribute [irreducible] tree186
private theorem sign_186 : 2*denominator*(computed denominator (FixedTape.midBox ibox186)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox186).gradient k).lo.natAbs ((computed denominator ibox186).gradient k).hi.natAbs : Int)*((ibox186 k).hi-(ibox186 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox186
    (computed denominator ibox186) (computed denominator (FixedTape.midBox ibox186))
    (by decide +kernel)
private theorem midpoint_even_186 : ∀ k, 2 ∣ (ibox186 k).lo+(ibox186 k).hi := by decide +kernel
private theorem accepted_186 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox186) tree186 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox186 midpoint_even_186
  simp only [tree186,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox186,candidate_valid h (FixedTape.midBox ibox186),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox186 106 (FixedTape.rowsAux denominator ibox186 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox186) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_186
private noncomputable def tree185 : TapeTree := .centered (candidateRows ibox185) (candidateRows (FixedTape.midBox ibox185))
attribute [irreducible] tree185
private theorem sign_185 : 2*denominator*(computed denominator (FixedTape.midBox ibox185)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox185).gradient k).lo.natAbs ((computed denominator ibox185).gradient k).hi.natAbs : Int)*((ibox185 k).hi-(ibox185 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox185
    (computed denominator ibox185) (computed denominator (FixedTape.midBox ibox185))
    (by decide +kernel)
private theorem midpoint_even_185 : ∀ k, 2 ∣ (ibox185 k).lo+(ibox185 k).hi := by decide +kernel
private theorem accepted_185 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox185) tree185 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox185 midpoint_even_185
  simp only [tree185,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox185,candidate_valid h (FixedTape.midBox ibox185),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox185 106 (FixedTape.rowsAux denominator ibox185 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox185) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_185
private noncomputable def tree184 : TapeTree := .split 3 (((114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree185 tree186
attribute [irreducible] tree184
private theorem accepted_184 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox184) tree184 = true := by
  simp only [tree184,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox184 3 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) false,decode_split denominator ibox184 3 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_185 h,accepted_186 h⟩
private noncomputable def tree183 : TapeTree := .split 2 (((495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree184 tree187
attribute [irreducible] tree183
private theorem accepted_183 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox183) tree183 = true := by
  simp only [tree183,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox183 2 (495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) false,decode_split denominator ibox183 2 (495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_184 h,accepted_187 h⟩
private noncomputable def tree182 : TapeTree := .centered (candidateRows ibox182) (candidateRows (FixedTape.midBox ibox182))
attribute [irreducible] tree182
private theorem sign_182 : 2*denominator*(computed denominator (FixedTape.midBox ibox182)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox182).gradient k).lo.natAbs ((computed denominator ibox182).gradient k).hi.natAbs : Int)*((ibox182 k).hi-(ibox182 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox182
    (computed denominator ibox182) (computed denominator (FixedTape.midBox ibox182))
    (by decide +kernel)
private theorem midpoint_even_182 : ∀ k, 2 ∣ (ibox182 k).lo+(ibox182 k).hi := by decide +kernel
private theorem accepted_182 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox182) tree182 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox182 midpoint_even_182
  simp only [tree182,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox182,candidate_valid h (FixedTape.midBox ibox182),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox182 106 (FixedTape.rowsAux denominator ibox182 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox182) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_182
private noncomputable def tree181 : TapeTree := .centered (candidateRows ibox181) (candidateRows (FixedTape.midBox ibox181))
attribute [irreducible] tree181
private theorem sign_181 : 2*denominator*(computed denominator (FixedTape.midBox ibox181)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox181).gradient k).lo.natAbs ((computed denominator ibox181).gradient k).hi.natAbs : Int)*((ibox181 k).hi-(ibox181 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox181
    (computed denominator ibox181) (computed denominator (FixedTape.midBox ibox181))
    (by decide +kernel)
private theorem midpoint_even_181 : ∀ k, 2 ∣ (ibox181 k).lo+(ibox181 k).hi := by decide +kernel
private theorem accepted_181 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox181) tree181 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox181 midpoint_even_181
  simp only [tree181,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox181,candidate_valid h (FixedTape.midBox ibox181),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox181 106 (FixedTape.rowsAux denominator ibox181 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox181) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_181
private noncomputable def tree180 : TapeTree := .split 0 (((307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) : ℚ)/(denominator : ℚ)) tree181 tree182
attribute [irreducible] tree180
private theorem accepted_180 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox180) tree180 = true := by
  simp only [tree180,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox180 0 (307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) false,decode_split denominator ibox180 0 (307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_181 h,accepted_182 h⟩
private noncomputable def tree179 : TapeTree := .centered (candidateRows ibox179) (candidateRows (FixedTape.midBox ibox179))
attribute [irreducible] tree179
private theorem sign_179 : 2*denominator*(computed denominator (FixedTape.midBox ibox179)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox179).gradient k).lo.natAbs ((computed denominator ibox179).gradient k).hi.natAbs : Int)*((ibox179 k).hi-(ibox179 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox179
    (computed denominator ibox179) (computed denominator (FixedTape.midBox ibox179))
    (by decide +kernel)
private theorem midpoint_even_179 : ∀ k, 2 ∣ (ibox179 k).lo+(ibox179 k).hi := by decide +kernel
private theorem accepted_179 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox179) tree179 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox179 midpoint_even_179
  simp only [tree179,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox179,candidate_valid h (FixedTape.midBox ibox179),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox179 106 (FixedTape.rowsAux denominator ibox179 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox179) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_179
private noncomputable def tree178 : TapeTree := .centered (candidateRows ibox178) (candidateRows (FixedTape.midBox ibox178))
attribute [irreducible] tree178
private theorem sign_178 : 2*denominator*(computed denominator (FixedTape.midBox ibox178)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox178).gradient k).lo.natAbs ((computed denominator ibox178).gradient k).hi.natAbs : Int)*((ibox178 k).hi-(ibox178 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox178
    (computed denominator ibox178) (computed denominator (FixedTape.midBox ibox178))
    (by decide +kernel)
private theorem midpoint_even_178 : ∀ k, 2 ∣ (ibox178 k).lo+(ibox178 k).hi := by decide +kernel
private theorem accepted_178 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox178) tree178 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox178 midpoint_even_178
  simp only [tree178,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox178,candidate_valid h (FixedTape.midBox ibox178),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox178 106 (FixedTape.rowsAux denominator ibox178 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox178) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_178
private noncomputable def tree177 : TapeTree := .split 0 (((307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) : ℚ)/(denominator : ℚ)) tree178 tree179
attribute [irreducible] tree177
private theorem accepted_177 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox177) tree177 = true := by
  simp only [tree177,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox177 0 (307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) false,decode_split denominator ibox177 0 (307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_178 h,accepted_179 h⟩
private noncomputable def tree176 : TapeTree := .split 3 (((38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree177 tree180
attribute [irreducible] tree176
private theorem accepted_176 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox176) tree176 = true := by
  simp only [tree176,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox176 3 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) false,decode_split denominator ibox176 3 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_177 h,accepted_180 h⟩
private noncomputable def tree175 : TapeTree := .centered (candidateRows ibox175) (candidateRows (FixedTape.midBox ibox175))
attribute [irreducible] tree175
private theorem sign_175 : 2*denominator*(computed denominator (FixedTape.midBox ibox175)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox175).gradient k).lo.natAbs ((computed denominator ibox175).gradient k).hi.natAbs : Int)*((ibox175 k).hi-(ibox175 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox175
    (computed denominator ibox175) (computed denominator (FixedTape.midBox ibox175))
    (by decide +kernel)
private theorem midpoint_even_175 : ∀ k, 2 ∣ (ibox175 k).lo+(ibox175 k).hi := by decide +kernel
private theorem accepted_175 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox175) tree175 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox175 midpoint_even_175
  simp only [tree175,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox175,candidate_valid h (FixedTape.midBox ibox175),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox175 106 (FixedTape.rowsAux denominator ibox175 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox175) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_175
private noncomputable def tree174 : TapeTree := .centered (candidateRows ibox174) (candidateRows (FixedTape.midBox ibox174))
attribute [irreducible] tree174
private theorem sign_174 : 2*denominator*(computed denominator (FixedTape.midBox ibox174)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox174).gradient k).lo.natAbs ((computed denominator ibox174).gradient k).hi.natAbs : Int)*((ibox174 k).hi-(ibox174 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox174
    (computed denominator ibox174) (computed denominator (FixedTape.midBox ibox174))
    (by decide +kernel)
private theorem midpoint_even_174 : ∀ k, 2 ∣ (ibox174 k).lo+(ibox174 k).hi := by decide +kernel
private theorem accepted_174 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox174) tree174 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox174 midpoint_even_174
  simp only [tree174,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox174,candidate_valid h (FixedTape.midBox ibox174),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox174 106 (FixedTape.rowsAux denominator ibox174 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox174) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_174
private noncomputable def tree173 : TapeTree := .centered (candidateRows ibox173) (candidateRows (FixedTape.midBox ibox173))
attribute [irreducible] tree173
private theorem sign_173 : 2*denominator*(computed denominator (FixedTape.midBox ibox173)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox173).gradient k).lo.natAbs ((computed denominator ibox173).gradient k).hi.natAbs : Int)*((ibox173 k).hi-(ibox173 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox173
    (computed denominator ibox173) (computed denominator (FixedTape.midBox ibox173))
    (by decide +kernel)
private theorem midpoint_even_173 : ∀ k, 2 ∣ (ibox173 k).lo+(ibox173 k).hi := by decide +kernel
private theorem accepted_173 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox173) tree173 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox173 midpoint_even_173
  simp only [tree173,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox173,candidate_valid h (FixedTape.midBox ibox173),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox173 106 (FixedTape.rowsAux denominator ibox173 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox173) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_173
private noncomputable def tree172 : TapeTree := .split 0 (((307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) : ℚ)/(denominator : ℚ)) tree173 tree174
attribute [irreducible] tree172
private theorem accepted_172 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox172) tree172 = true := by
  simp only [tree172,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox172 0 (307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) false,decode_split denominator ibox172 0 (307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_173 h,accepted_174 h⟩
private noncomputable def tree171 : TapeTree := .split 3 (((38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree172 tree175
attribute [irreducible] tree171
private theorem accepted_171 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox171) tree171 = true := by
  simp only [tree171,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox171 3 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) false,decode_split denominator ibox171 3 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_172 h,accepted_175 h⟩
private noncomputable def tree170 : TapeTree := .split 2 (((495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree171 tree176
attribute [irreducible] tree170
private theorem accepted_170 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox170) tree170 = true := by
  simp only [tree170,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox170 2 (495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) false,decode_split denominator ibox170 2 (495014574431232466016876168969040718036868257058239788827919037942302987442058626776704695979212800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_171 h,accepted_176 h⟩
private noncomputable def tree169 : TapeTree := .split 3 (((76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree170 tree183
attribute [irreducible] tree169
private theorem accepted_169 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox169) tree169 = true := by
  simp only [tree169,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox169 3 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) false,decode_split denominator ibox169 3 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_170 h,accepted_183 h⟩
private noncomputable def tree168 : TapeTree := .split 2 (((533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree169 tree190
attribute [irreducible] tree168
private theorem accepted_168 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox168) tree168 = true := by
  simp only [tree168,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox168 2 (533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 : Int) false,decode_split denominator ibox168 2 (533092618618250348018174335812813080962781199908873618737758963937864755706832367297989672592998400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_169 h,accepted_190 h⟩
private noncomputable def tree167 : TapeTree := .split 3 (((152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree168 tree213
attribute [irreducible] tree167
private theorem accepted_167 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox167) tree167 = true := by
  simp only [tree167,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox167 3 (152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) false,decode_split denominator ibox167 3 (152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_168 h,accepted_213 h⟩
private noncomputable def tree166 : TapeTree := .centered (candidateRows ibox166) (candidateRows (FixedTape.midBox ibox166))
attribute [irreducible] tree166
private theorem sign_166 : 2*denominator*(computed denominator (FixedTape.midBox ibox166)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox166).gradient k).lo.natAbs ((computed denominator ibox166).gradient k).hi.natAbs : Int)*((ibox166 k).hi-(ibox166 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox166
    (computed denominator ibox166) (computed denominator (FixedTape.midBox ibox166))
    (by decide +kernel)
private theorem midpoint_even_166 : ∀ k, 2 ∣ (ibox166 k).lo+(ibox166 k).hi := by decide +kernel
private theorem accepted_166 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox166) tree166 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox166 midpoint_even_166
  simp only [tree166,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox166,candidate_valid h (FixedTape.midBox ibox166),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox166 106 (FixedTape.rowsAux denominator ibox166 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox166) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_166
private noncomputable def tree165 : TapeTree := .centered (candidateRows ibox165) (candidateRows (FixedTape.midBox ibox165))
attribute [irreducible] tree165
private theorem sign_165 : 2*denominator*(computed denominator (FixedTape.midBox ibox165)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox165).gradient k).lo.natAbs ((computed denominator ibox165).gradient k).hi.natAbs : Int)*((ibox165 k).hi-(ibox165 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox165
    (computed denominator ibox165) (computed denominator (FixedTape.midBox ibox165))
    (by decide +kernel)
private theorem midpoint_even_165 : ∀ k, 2 ∣ (ibox165 k).lo+(ibox165 k).hi := by decide +kernel
private theorem accepted_165 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox165) tree165 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox165 midpoint_even_165
  simp only [tree165,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox165,candidate_valid h (FixedTape.midBox ibox165),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox165 106 (FixedTape.rowsAux denominator ibox165 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox165) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_165
private noncomputable def tree164 : TapeTree := .split 2 (((418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree165 tree166
attribute [irreducible] tree164
private theorem accepted_164 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox164) tree164 = true := by
  simp only [tree164,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox164 2 (418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) false,decode_split denominator ibox164 2 (418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_165 h,accepted_166 h⟩
private noncomputable def tree163 : TapeTree := .centered (candidateRows ibox163) (candidateRows (FixedTape.midBox ibox163))
attribute [irreducible] tree163
private theorem sign_163 : 2*denominator*(computed denominator (FixedTape.midBox ibox163)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox163).gradient k).lo.natAbs ((computed denominator ibox163).gradient k).hi.natAbs : Int)*((ibox163 k).hi-(ibox163 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox163
    (computed denominator ibox163) (computed denominator (FixedTape.midBox ibox163))
    (by decide +kernel)
private theorem midpoint_even_163 : ∀ k, 2 ∣ (ibox163 k).lo+(ibox163 k).hi := by decide +kernel
private theorem accepted_163 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox163) tree163 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox163 midpoint_even_163
  simp only [tree163,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox163,candidate_valid h (FixedTape.midBox ibox163),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox163 106 (FixedTape.rowsAux denominator ibox163 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox163) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_163
private noncomputable def tree162 : TapeTree := .centered (candidateRows ibox162) (candidateRows (FixedTape.midBox ibox162))
attribute [irreducible] tree162
private theorem sign_162 : 2*denominator*(computed denominator (FixedTape.midBox ibox162)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox162).gradient k).lo.natAbs ((computed denominator ibox162).gradient k).hi.natAbs : Int)*((ibox162 k).hi-(ibox162 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox162
    (computed denominator ibox162) (computed denominator (FixedTape.midBox ibox162))
    (by decide +kernel)
private theorem midpoint_even_162 : ∀ k, 2 ∣ (ibox162 k).lo+(ibox162 k).hi := by decide +kernel
private theorem accepted_162 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox162) tree162 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox162 midpoint_even_162
  simp only [tree162,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox162,candidate_valid h (FixedTape.midBox ibox162),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox162 106 (FixedTape.rowsAux denominator ibox162 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox162) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_162
private noncomputable def tree161 : TapeTree := .split 2 (((418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree162 tree163
attribute [irreducible] tree161
private theorem accepted_161 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox161) tree161 = true := by
  simp only [tree161,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox161 2 (418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) false,decode_split denominator ibox161 2 (418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_162 h,accepted_163 h⟩
private noncomputable def tree160 : TapeTree := .split 3 (((228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree161 tree164
attribute [irreducible] tree160
private theorem accepted_160 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox160) tree160 = true := by
  simp only [tree160,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox160 3 (228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) false,decode_split denominator ibox160 3 (228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_161 h,accepted_164 h⟩
private noncomputable def tree159 : TapeTree := .centered (candidateRows ibox159) (candidateRows (FixedTape.midBox ibox159))
attribute [irreducible] tree159
private theorem sign_159 : 2*denominator*(computed denominator (FixedTape.midBox ibox159)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox159).gradient k).lo.natAbs ((computed denominator ibox159).gradient k).hi.natAbs : Int)*((ibox159 k).hi-(ibox159 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox159
    (computed denominator ibox159) (computed denominator (FixedTape.midBox ibox159))
    (by decide +kernel)
private theorem midpoint_even_159 : ∀ k, 2 ∣ (ibox159 k).lo+(ibox159 k).hi := by decide +kernel
private theorem accepted_159 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox159) tree159 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox159 midpoint_even_159
  simp only [tree159,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox159,candidate_valid h (FixedTape.midBox ibox159),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox159 106 (FixedTape.rowsAux denominator ibox159 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox159) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_159
private noncomputable def tree158 : TapeTree := .centered (candidateRows ibox158) (candidateRows (FixedTape.midBox ibox158))
attribute [irreducible] tree158
private theorem sign_158 : 2*denominator*(computed denominator (FixedTape.midBox ibox158)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox158).gradient k).lo.natAbs ((computed denominator ibox158).gradient k).hi.natAbs : Int)*((ibox158 k).hi-(ibox158 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox158
    (computed denominator ibox158) (computed denominator (FixedTape.midBox ibox158))
    (by decide +kernel)
private theorem midpoint_even_158 : ∀ k, 2 ∣ (ibox158 k).lo+(ibox158 k).hi := by decide +kernel
private theorem accepted_158 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox158) tree158 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox158 midpoint_even_158
  simp only [tree158,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox158,candidate_valid h (FixedTape.midBox ibox158),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox158 106 (FixedTape.rowsAux denominator ibox158 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox158) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_158
private noncomputable def tree157 : TapeTree := .split 2 (((342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree158 tree159
attribute [irreducible] tree157
private theorem accepted_157 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox157) tree157 = true := by
  simp only [tree157,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox157 2 (342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 : Int) false,decode_split denominator ibox157 2 (342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_158 h,accepted_159 h⟩
private noncomputable def tree156 : TapeTree := .centered (candidateRows ibox156) (candidateRows (FixedTape.midBox ibox156))
attribute [irreducible] tree156
private theorem sign_156 : 2*denominator*(computed denominator (FixedTape.midBox ibox156)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox156).gradient k).lo.natAbs ((computed denominator ibox156).gradient k).hi.natAbs : Int)*((ibox156 k).hi-(ibox156 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox156
    (computed denominator ibox156) (computed denominator (FixedTape.midBox ibox156))
    (by decide +kernel)
private theorem midpoint_even_156 : ∀ k, 2 ∣ (ibox156 k).lo+(ibox156 k).hi := by decide +kernel
private theorem accepted_156 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox156) tree156 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox156 midpoint_even_156
  simp only [tree156,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox156,candidate_valid h (FixedTape.midBox ibox156),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox156 106 (FixedTape.rowsAux denominator ibox156 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox156) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_156
private noncomputable def tree155 : TapeTree := .centered (candidateRows ibox155) (candidateRows (FixedTape.midBox ibox155))
attribute [irreducible] tree155
private theorem sign_155 : 2*denominator*(computed denominator (FixedTape.midBox ibox155)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox155).gradient k).lo.natAbs ((computed denominator ibox155).gradient k).hi.natAbs : Int)*((ibox155 k).hi-(ibox155 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox155
    (computed denominator ibox155) (computed denominator (FixedTape.midBox ibox155))
    (by decide +kernel)
private theorem midpoint_even_155 : ∀ k, 2 ∣ (ibox155 k).lo+(ibox155 k).hi := by decide +kernel
private theorem accepted_155 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox155) tree155 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox155 midpoint_even_155
  simp only [tree155,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox155,candidate_valid h (FixedTape.midBox ibox155),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox155 106 (FixedTape.rowsAux denominator ibox155 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox155) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_155
private noncomputable def tree154 : TapeTree := .split 2 (((342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree155 tree156
attribute [irreducible] tree154
private theorem accepted_154 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox154) tree154 = true := by
  simp only [tree154,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox154 2 (342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 : Int) false,decode_split denominator ibox154 2 (342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_155 h,accepted_156 h⟩
private noncomputable def tree153 : TapeTree := .split 3 (((228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree154 tree157
attribute [irreducible] tree153
private theorem accepted_153 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox153) tree153 = true := by
  simp only [tree153,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox153 3 (228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) false,decode_split denominator ibox153 3 (228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_154 h,accepted_157 h⟩
private noncomputable def tree152 : TapeTree := .split 2 (((380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree153 tree160
attribute [irreducible] tree152
private theorem accepted_152 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox152) tree152 = true := by
  simp only [tree152,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox152 2 (380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) false,decode_split denominator ibox152 2 (380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_153 h,accepted_160 h⟩
private noncomputable def tree151 : TapeTree := .centered (candidateRows ibox151) (candidateRows (FixedTape.midBox ibox151))
attribute [irreducible] tree151
private theorem sign_151 : 2*denominator*(computed denominator (FixedTape.midBox ibox151)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox151).gradient k).lo.natAbs ((computed denominator ibox151).gradient k).hi.natAbs : Int)*((ibox151 k).hi-(ibox151 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox151
    (computed denominator ibox151) (computed denominator (FixedTape.midBox ibox151))
    (by decide +kernel)
private theorem midpoint_even_151 : ∀ k, 2 ∣ (ibox151 k).lo+(ibox151 k).hi := by decide +kernel
private theorem accepted_151 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox151) tree151 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox151 midpoint_even_151
  simp only [tree151,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox151,candidate_valid h (FixedTape.midBox ibox151),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox151 106 (FixedTape.rowsAux denominator ibox151 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox151) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_151
private noncomputable def tree150 : TapeTree := .centered (candidateRows ibox150) (candidateRows (FixedTape.midBox ibox150))
attribute [irreducible] tree150
private theorem sign_150 : 2*denominator*(computed denominator (FixedTape.midBox ibox150)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox150).gradient k).lo.natAbs ((computed denominator ibox150).gradient k).hi.natAbs : Int)*((ibox150 k).hi-(ibox150 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox150
    (computed denominator ibox150) (computed denominator (FixedTape.midBox ibox150))
    (by decide +kernel)
private theorem midpoint_even_150 : ∀ k, 2 ∣ (ibox150 k).lo+(ibox150 k).hi := by decide +kernel
private theorem accepted_150 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox150) tree150 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox150 midpoint_even_150
  simp only [tree150,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox150,candidate_valid h (FixedTape.midBox ibox150),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox150 106 (FixedTape.rowsAux denominator ibox150 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox150) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_150
private noncomputable def tree149 : TapeTree := .split 3 (((114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree150 tree151
attribute [irreducible] tree149
private theorem accepted_149 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox149) tree149 = true := by
  simp only [tree149,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox149 3 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) false,decode_split denominator ibox149 3 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_150 h,accepted_151 h⟩
private noncomputable def tree148 : TapeTree := .centered (candidateRows ibox148) (candidateRows (FixedTape.midBox ibox148))
attribute [irreducible] tree148
private theorem sign_148 : 2*denominator*(computed denominator (FixedTape.midBox ibox148)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox148).gradient k).lo.natAbs ((computed denominator ibox148).gradient k).hi.natAbs : Int)*((ibox148 k).hi-(ibox148 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox148
    (computed denominator ibox148) (computed denominator (FixedTape.midBox ibox148))
    (by decide +kernel)
private theorem midpoint_even_148 : ∀ k, 2 ∣ (ibox148 k).lo+(ibox148 k).hi := by decide +kernel
private theorem accepted_148 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox148) tree148 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox148 midpoint_even_148
  simp only [tree148,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox148,candidate_valid h (FixedTape.midBox ibox148),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox148 106 (FixedTape.rowsAux denominator ibox148 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox148) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_148
private noncomputable def tree147 : TapeTree := .centered (candidateRows ibox147) (candidateRows (FixedTape.midBox ibox147))
attribute [irreducible] tree147
private theorem sign_147 : 2*denominator*(computed denominator (FixedTape.midBox ibox147)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox147).gradient k).lo.natAbs ((computed denominator ibox147).gradient k).hi.natAbs : Int)*((ibox147 k).hi-(ibox147 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox147
    (computed denominator ibox147) (computed denominator (FixedTape.midBox ibox147))
    (by decide +kernel)
private theorem midpoint_even_147 : ∀ k, 2 ∣ (ibox147 k).lo+(ibox147 k).hi := by decide +kernel
private theorem accepted_147 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox147) tree147 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox147 midpoint_even_147
  simp only [tree147,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox147,candidate_valid h (FixedTape.midBox ibox147),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox147 106 (FixedTape.rowsAux denominator ibox147 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox147) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_147
private noncomputable def tree146 : TapeTree := .split 3 (((114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree147 tree148
attribute [irreducible] tree146
private theorem accepted_146 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox146) tree146 = true := by
  simp only [tree146,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox146 3 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) false,decode_split denominator ibox146 3 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_147 h,accepted_148 h⟩
private noncomputable def tree145 : TapeTree := .split 2 (((418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree146 tree149
attribute [irreducible] tree145
private theorem accepted_145 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox145) tree145 = true := by
  simp only [tree145,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox145 2 (418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) false,decode_split denominator ibox145 2 (418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_146 h,accepted_149 h⟩
private noncomputable def tree144 : TapeTree := .centered (candidateRows ibox144) (candidateRows (FixedTape.midBox ibox144))
attribute [irreducible] tree144
private theorem sign_144 : 2*denominator*(computed denominator (FixedTape.midBox ibox144)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox144).gradient k).lo.natAbs ((computed denominator ibox144).gradient k).hi.natAbs : Int)*((ibox144 k).hi-(ibox144 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox144
    (computed denominator ibox144) (computed denominator (FixedTape.midBox ibox144))
    (by decide +kernel)
private theorem midpoint_even_144 : ∀ k, 2 ∣ (ibox144 k).lo+(ibox144 k).hi := by decide +kernel
private theorem accepted_144 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox144) tree144 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox144 midpoint_even_144
  simp only [tree144,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox144,candidate_valid h (FixedTape.midBox ibox144),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox144 106 (FixedTape.rowsAux denominator ibox144 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox144) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_144
private noncomputable def tree143 : TapeTree := .centered (candidateRows ibox143) (candidateRows (FixedTape.midBox ibox143))
attribute [irreducible] tree143
private theorem sign_143 : 2*denominator*(computed denominator (FixedTape.midBox ibox143)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox143).gradient k).lo.natAbs ((computed denominator ibox143).gradient k).hi.natAbs : Int)*((ibox143 k).hi-(ibox143 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox143
    (computed denominator ibox143) (computed denominator (FixedTape.midBox ibox143))
    (by decide +kernel)
private theorem midpoint_even_143 : ∀ k, 2 ∣ (ibox143 k).lo+(ibox143 k).hi := by decide +kernel
private theorem accepted_143 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox143) tree143 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox143 midpoint_even_143
  simp only [tree143,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox143,candidate_valid h (FixedTape.midBox ibox143),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox143 106 (FixedTape.rowsAux denominator ibox143 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox143) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_143
private noncomputable def tree142 : TapeTree := .centered (candidateRows ibox142) (candidateRows (FixedTape.midBox ibox142))
attribute [irreducible] tree142
private theorem sign_142 : 2*denominator*(computed denominator (FixedTape.midBox ibox142)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox142).gradient k).lo.natAbs ((computed denominator ibox142).gradient k).hi.natAbs : Int)*((ibox142 k).hi-(ibox142 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox142
    (computed denominator ibox142) (computed denominator (FixedTape.midBox ibox142))
    (by decide +kernel)
private theorem midpoint_even_142 : ∀ k, 2 ∣ (ibox142 k).lo+(ibox142 k).hi := by decide +kernel
private theorem accepted_142 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox142) tree142 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox142 midpoint_even_142
  simp only [tree142,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox142,candidate_valid h (FixedTape.midBox ibox142),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox142 106 (FixedTape.rowsAux denominator ibox142 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox142) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_142
private noncomputable def tree141 : TapeTree := .split 0 (((307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) : ℚ)/(denominator : ℚ)) tree142 tree143
attribute [irreducible] tree141
private theorem accepted_141 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox141) tree141 = true := by
  simp only [tree141,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox141 0 (307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) false,decode_split denominator ibox141 0 (307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_142 h,accepted_143 h⟩
private noncomputable def tree140 : TapeTree := .split 3 (((38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree141 tree144
attribute [irreducible] tree140
private theorem accepted_140 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox140) tree140 = true := by
  simp only [tree140,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox140 3 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) false,decode_split denominator ibox140 3 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_141 h,accepted_144 h⟩
private noncomputable def tree139 : TapeTree := .centered (candidateRows ibox139) (candidateRows (FixedTape.midBox ibox139))
attribute [irreducible] tree139
private theorem sign_139 : 2*denominator*(computed denominator (FixedTape.midBox ibox139)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox139).gradient k).lo.natAbs ((computed denominator ibox139).gradient k).hi.natAbs : Int)*((ibox139 k).hi-(ibox139 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox139
    (computed denominator ibox139) (computed denominator (FixedTape.midBox ibox139))
    (by decide +kernel)
private theorem midpoint_even_139 : ∀ k, 2 ∣ (ibox139 k).lo+(ibox139 k).hi := by decide +kernel
private theorem accepted_139 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox139) tree139 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox139 midpoint_even_139
  simp only [tree139,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox139,candidate_valid h (FixedTape.midBox ibox139),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox139 106 (FixedTape.rowsAux denominator ibox139 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox139) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_139
private noncomputable def tree138 : TapeTree := .centered (candidateRows ibox138) (candidateRows (FixedTape.midBox ibox138))
attribute [irreducible] tree138
private theorem sign_138 : 2*denominator*(computed denominator (FixedTape.midBox ibox138)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox138).gradient k).lo.natAbs ((computed denominator ibox138).gradient k).hi.natAbs : Int)*((ibox138 k).hi-(ibox138 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox138
    (computed denominator ibox138) (computed denominator (FixedTape.midBox ibox138))
    (by decide +kernel)
private theorem midpoint_even_138 : ∀ k, 2 ∣ (ibox138 k).lo+(ibox138 k).hi := by decide +kernel
private theorem accepted_138 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox138) tree138 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox138 midpoint_even_138
  simp only [tree138,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox138,candidate_valid h (FixedTape.midBox ibox138),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox138 106 (FixedTape.rowsAux denominator ibox138 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox138) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_138
private noncomputable def tree137 : TapeTree := .centered (candidateRows ibox137) (candidateRows (FixedTape.midBox ibox137))
attribute [irreducible] tree137
private theorem sign_137 : 2*denominator*(computed denominator (FixedTape.midBox ibox137)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox137).gradient k).lo.natAbs ((computed denominator ibox137).gradient k).hi.natAbs : Int)*((ibox137 k).hi-(ibox137 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox137
    (computed denominator ibox137) (computed denominator (FixedTape.midBox ibox137))
    (by decide +kernel)
private theorem midpoint_even_137 : ∀ k, 2 ∣ (ibox137 k).lo+(ibox137 k).hi := by decide +kernel
private theorem accepted_137 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox137) tree137 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox137 midpoint_even_137
  simp only [tree137,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox137,candidate_valid h (FixedTape.midBox ibox137),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox137 106 (FixedTape.rowsAux denominator ibox137 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox137) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_137
private noncomputable def tree136 : TapeTree := .split 0 (((307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) : ℚ)/(denominator : ℚ)) tree137 tree138
attribute [irreducible] tree136
private theorem accepted_136 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox136) tree136 = true := by
  simp only [tree136,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox136 0 (307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) false,decode_split denominator ibox136 0 (307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_137 h,accepted_138 h⟩
private noncomputable def tree135 : TapeTree := .split 3 (((38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree136 tree139
attribute [irreducible] tree135
private theorem accepted_135 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox135) tree135 = true := by
  simp only [tree135,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox135 3 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) false,decode_split denominator ibox135 3 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_136 h,accepted_139 h⟩
private noncomputable def tree134 : TapeTree := .split 2 (((418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree135 tree140
attribute [irreducible] tree134
private theorem accepted_134 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox134) tree134 = true := by
  simp only [tree134,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox134 2 (418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) false,decode_split denominator ibox134 2 (418858486057196702014279835281495992185042371356972129008239185951179450912511145734134742751641600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_135 h,accepted_140 h⟩
private noncomputable def tree133 : TapeTree := .split 3 (((76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree134 tree145
attribute [irreducible] tree133
private theorem accepted_133 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox133) tree133 = true := by
  simp only [tree133,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox133 3 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) false,decode_split denominator ibox133 3 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_134 h,accepted_145 h⟩
private noncomputable def tree132 : TapeTree := .centered (candidateRows ibox132) (candidateRows (FixedTape.midBox ibox132))
attribute [irreducible] tree132
private theorem sign_132 : 2*denominator*(computed denominator (FixedTape.midBox ibox132)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox132).gradient k).lo.natAbs ((computed denominator ibox132).gradient k).hi.natAbs : Int)*((ibox132 k).hi-(ibox132 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox132
    (computed denominator ibox132) (computed denominator (FixedTape.midBox ibox132))
    (by decide +kernel)
private theorem midpoint_even_132 : ∀ k, 2 ∣ (ibox132 k).lo+(ibox132 k).hi := by decide +kernel
private theorem accepted_132 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox132) tree132 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox132 midpoint_even_132
  simp only [tree132,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox132,candidate_valid h (FixedTape.midBox ibox132),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox132 106 (FixedTape.rowsAux denominator ibox132 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox132) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_132
private noncomputable def tree131 : TapeTree := .centered (candidateRows ibox131) (candidateRows (FixedTape.midBox ibox131))
attribute [irreducible] tree131
private theorem sign_131 : 2*denominator*(computed denominator (FixedTape.midBox ibox131)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox131).gradient k).lo.natAbs ((computed denominator ibox131).gradient k).hi.natAbs : Int)*((ibox131 k).hi-(ibox131 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox131
    (computed denominator ibox131) (computed denominator (FixedTape.midBox ibox131))
    (by decide +kernel)
private theorem midpoint_even_131 : ∀ k, 2 ∣ (ibox131 k).lo+(ibox131 k).hi := by decide +kernel
private theorem accepted_131 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox131) tree131 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox131 midpoint_even_131
  simp only [tree131,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox131,candidate_valid h (FixedTape.midBox ibox131),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox131 106 (FixedTape.rowsAux denominator ibox131 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox131) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_131
private noncomputable def tree130 : TapeTree := .split 3 (((114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree131 tree132
attribute [irreducible] tree130
private theorem accepted_130 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox130) tree130 = true := by
  simp only [tree130,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox130 3 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) false,decode_split denominator ibox130 3 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_131 h,accepted_132 h⟩
private noncomputable def tree129 : TapeTree := .centered (candidateRows ibox129) (candidateRows (FixedTape.midBox ibox129))
attribute [irreducible] tree129
private theorem sign_129 : 2*denominator*(computed denominator (FixedTape.midBox ibox129)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox129).gradient k).lo.natAbs ((computed denominator ibox129).gradient k).hi.natAbs : Int)*((ibox129 k).hi-(ibox129 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox129
    (computed denominator ibox129) (computed denominator (FixedTape.midBox ibox129))
    (by decide +kernel)
private theorem midpoint_even_129 : ∀ k, 2 ∣ (ibox129 k).lo+(ibox129 k).hi := by decide +kernel
private theorem accepted_129 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox129) tree129 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox129 midpoint_even_129
  simp only [tree129,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox129,candidate_valid h (FixedTape.midBox ibox129),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox129 106 (FixedTape.rowsAux denominator ibox129 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox129) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_129
private noncomputable def tree128 : TapeTree := .centered (candidateRows ibox128) (candidateRows (FixedTape.midBox ibox128))
attribute [irreducible] tree128
private theorem sign_128 : 2*denominator*(computed denominator (FixedTape.midBox ibox128)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox128).gradient k).lo.natAbs ((computed denominator ibox128).gradient k).hi.natAbs : Int)*((ibox128 k).hi-(ibox128 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox128
    (computed denominator ibox128) (computed denominator (FixedTape.midBox ibox128))
    (by decide +kernel)
private theorem midpoint_even_128 : ∀ k, 2 ∣ (ibox128 k).lo+(ibox128 k).hi := by decide +kernel
private theorem accepted_128 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox128) tree128 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox128 midpoint_even_128
  simp only [tree128,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox128,candidate_valid h (FixedTape.midBox ibox128),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox128 106 (FixedTape.rowsAux denominator ibox128 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox128) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_128
private noncomputable def tree127 : TapeTree := .split 3 (((114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree128 tree129
attribute [irreducible] tree127
private theorem accepted_127 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox127) tree127 = true := by
  simp only [tree127,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox127 3 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) false,decode_split denominator ibox127 3 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_128 h,accepted_129 h⟩
private noncomputable def tree126 : TapeTree := .split 2 (((342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree127 tree130
attribute [irreducible] tree126
private theorem accepted_126 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox126) tree126 = true := by
  simp only [tree126,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox126 2 (342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 : Int) false,decode_split denominator ibox126 2 (342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_127 h,accepted_130 h⟩
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
private noncomputable def tree123 : TapeTree := .centered (candidateRows ibox123) (candidateRows (FixedTape.midBox ibox123))
attribute [irreducible] tree123
private theorem sign_123 : 2*denominator*(computed denominator (FixedTape.midBox ibox123)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox123).gradient k).lo.natAbs ((computed denominator ibox123).gradient k).hi.natAbs : Int)*((ibox123 k).hi-(ibox123 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox123
    (computed denominator ibox123) (computed denominator (FixedTape.midBox ibox123))
    (by decide +kernel)
private theorem midpoint_even_123 : ∀ k, 2 ∣ (ibox123 k).lo+(ibox123 k).hi := by decide +kernel
private theorem accepted_123 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox123) tree123 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox123 midpoint_even_123
  simp only [tree123,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox123,candidate_valid h (FixedTape.midBox ibox123),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox123 106 (FixedTape.rowsAux denominator ibox123 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox123) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_123
private noncomputable def tree122 : TapeTree := .split 0 (((307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) : ℚ)/(denominator : ℚ)) tree123 tree124
attribute [irreducible] tree122
private theorem accepted_122 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox122) tree122 = true := by
  simp only [tree122,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox122 0 (307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) false,decode_split denominator ibox122 0 (307797523845061192535536615577622866292107304697363231284303214792748341558960538247443819748771988648012472647680000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_123 h,accepted_124 h⟩
private noncomputable def tree121 : TapeTree := .split 3 (((38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree122 tree125
attribute [irreducible] tree121
private theorem accepted_121 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox121) tree121 = true := by
  simp only [tree121,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox121 3 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) false,decode_split denominator ibox121 3 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_122 h,accepted_125 h⟩
private noncomputable def tree120 : TapeTree := .centered (candidateRows ibox120) (candidateRows (FixedTape.midBox ibox120))
attribute [irreducible] tree120
private theorem sign_120 : 2*denominator*(computed denominator (FixedTape.midBox ibox120)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox120).gradient k).lo.natAbs ((computed denominator ibox120).gradient k).hi.natAbs : Int)*((ibox120 k).hi-(ibox120 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox120
    (computed denominator ibox120) (computed denominator (FixedTape.midBox ibox120))
    (by decide +kernel)
private theorem midpoint_even_120 : ∀ k, 2 ∣ (ibox120 k).lo+(ibox120 k).hi := by decide +kernel
private theorem accepted_120 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox120) tree120 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox120 midpoint_even_120
  simp only [tree120,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox120,candidate_valid h (FixedTape.midBox ibox120),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox120 106 (FixedTape.rowsAux denominator ibox120 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox120) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_120
private noncomputable def tree119 : TapeTree := .centered (candidateRows ibox119) (candidateRows (FixedTape.midBox ibox119))
attribute [irreducible] tree119
private theorem sign_119 : 2*denominator*(computed denominator (FixedTape.midBox ibox119)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox119).gradient k).lo.natAbs ((computed denominator ibox119).gradient k).hi.natAbs : Int)*((ibox119 k).hi-(ibox119 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox119
    (computed denominator ibox119) (computed denominator (FixedTape.midBox ibox119))
    (by decide +kernel)
private theorem midpoint_even_119 : ∀ k, 2 ∣ (ibox119 k).lo+(ibox119 k).hi := by decide +kernel
private theorem accepted_119 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox119) tree119 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox119 midpoint_even_119
  simp only [tree119,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox119,candidate_valid h (FixedTape.midBox ibox119),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox119 106 (FixedTape.rowsAux denominator ibox119 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox119) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_119
private noncomputable def tree118 : TapeTree := .split 3 (((38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree119 tree120
attribute [irreducible] tree118
private theorem accepted_118 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox118) tree118 = true := by
  simp only [tree118,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox118 3 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) false,decode_split denominator ibox118 3 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_119 h,accepted_120 h⟩
private noncomputable def tree117 : TapeTree := .split 2 (((342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree118 tree121
attribute [irreducible] tree117
private theorem accepted_117 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox117) tree117 = true := by
  simp only [tree117,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox117 2 (342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 : Int) false,decode_split denominator ibox117 2 (342702397683160938011683501593951266333216485655704469188559333960055914382963664691564789524070400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_118 h,accepted_121 h⟩
private noncomputable def tree116 : TapeTree := .split 3 (((76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree117 tree126
attribute [irreducible] tree116
private theorem accepted_116 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox116) tree116 = true := by
  simp only [tree116,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox116 3 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) false,decode_split denominator ibox116 3 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_117 h,accepted_126 h⟩
private noncomputable def tree115 : TapeTree := .split 2 (((380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree116 tree133
attribute [irreducible] tree115
private theorem accepted_115 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox115) tree115 = true := by
  simp only [tree115,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox115 2 (380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) false,decode_split denominator ibox115 2 (380780441870178820012981668437723629259129428506338299098399259955617682647737405212849766137856000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_116 h,accepted_133 h⟩
private noncomputable def tree114 : TapeTree := .split 3 (((152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree115 tree152
attribute [irreducible] tree114
private theorem accepted_114 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox114) tree114 = true := by
  simp only [tree114,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox114 3 (152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) false,decode_split denominator ibox114 3 (152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_115 h,accepted_152 h⟩
private noncomputable def tree113 : TapeTree := .split 2 (((456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree114 tree167
attribute [irreducible] tree113
private theorem accepted_113 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox113) tree113 = true := by
  simp only [tree113,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox113 2 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) false,decode_split denominator ibox113 2 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_114 h,accepted_167 h⟩
private noncomputable def tree112 : TapeTree := .split 3 (((304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree113 tree236
attribute [irreducible] tree112
private theorem accepted_112 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox112) tree112 = true := by
  simp only [tree112,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox112 3 (304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) false,decode_split denominator ibox112 3 (304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_113 h,accepted_236 h⟩
private noncomputable def tree111 : TapeTree := .centered (candidateRows ibox111) (candidateRows (FixedTape.midBox ibox111))
attribute [irreducible] tree111
private theorem sign_111 : 2*denominator*(computed denominator (FixedTape.midBox ibox111)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox111).gradient k).lo.natAbs ((computed denominator ibox111).gradient k).hi.natAbs : Int)*((ibox111 k).hi-(ibox111 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox111
    (computed denominator ibox111) (computed denominator (FixedTape.midBox ibox111))
    (by decide +kernel)
private theorem midpoint_even_111 : ∀ k, 2 ∣ (ibox111 k).lo+(ibox111 k).hi := by decide +kernel
private theorem accepted_111 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox111) tree111 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox111 midpoint_even_111
  simp only [tree111,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox111,candidate_valid h (FixedTape.midBox ibox111),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox111 106 (FixedTape.rowsAux denominator ibox111 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox111) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_111
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
private noncomputable def tree109 : TapeTree := .split 2 (((266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree110 tree111
attribute [irreducible] tree109
private theorem accepted_109 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox109) tree109 = true := by
  simp only [tree109,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox109 2 (266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 : Int) false,decode_split denominator ibox109 2 (266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_110 h,accepted_111 h⟩
private noncomputable def tree108 : TapeTree := .centered (candidateRows ibox108) (candidateRows (FixedTape.midBox ibox108))
attribute [irreducible] tree108
private theorem sign_108 : 2*denominator*(computed denominator (FixedTape.midBox ibox108)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox108).gradient k).lo.natAbs ((computed denominator ibox108).gradient k).hi.natAbs : Int)*((ibox108 k).hi-(ibox108 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox108
    (computed denominator ibox108) (computed denominator (FixedTape.midBox ibox108))
    (by decide +kernel)
private theorem midpoint_even_108 : ∀ k, 2 ∣ (ibox108 k).lo+(ibox108 k).hi := by decide +kernel
private theorem accepted_108 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox108) tree108 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox108 midpoint_even_108
  simp only [tree108,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox108,candidate_valid h (FixedTape.midBox ibox108),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox108 106 (FixedTape.rowsAux denominator ibox108 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox108) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_108
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
private noncomputable def tree106 : TapeTree := .split 2 (((266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree107 tree108
attribute [irreducible] tree106
private theorem accepted_106 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox106) tree106 = true := by
  simp only [tree106,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox106 2 (266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 : Int) false,decode_split denominator ibox106 2 (266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_107 h,accepted_108 h⟩
private noncomputable def tree105 : TapeTree := .split 3 (((456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree106 tree109
attribute [irreducible] tree105
private theorem accepted_105 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox105) tree105 = true := by
  simp only [tree105,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox105 3 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) false,decode_split denominator ibox105 3 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_106 h,accepted_109 h⟩
private noncomputable def tree104 : TapeTree := .centered (candidateRows ibox104) (candidateRows (FixedTape.midBox ibox104))
attribute [irreducible] tree104
private theorem sign_104 : 2*denominator*(computed denominator (FixedTape.midBox ibox104)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox104).gradient k).lo.natAbs ((computed denominator ibox104).gradient k).hi.natAbs : Int)*((ibox104 k).hi-(ibox104 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox104
    (computed denominator ibox104) (computed denominator (FixedTape.midBox ibox104))
    (by decide +kernel)
private theorem midpoint_even_104 : ∀ k, 2 ∣ (ibox104 k).lo+(ibox104 k).hi := by decide +kernel
private theorem accepted_104 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox104) tree104 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox104 midpoint_even_104
  simp only [tree104,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox104,candidate_valid h (FixedTape.midBox ibox104),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox104 106 (FixedTape.rowsAux denominator ibox104 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox104) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_104
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
private noncomputable def tree102 : TapeTree := .split 2 (((190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree103 tree104
attribute [irreducible] tree102
private theorem accepted_102 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox102) tree102 = true := by
  simp only [tree102,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox102 2 (190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) false,decode_split denominator ibox102 2 (190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_103 h,accepted_104 h⟩
private noncomputable def tree101 : TapeTree := .centered (candidateRows ibox101) (candidateRows (FixedTape.midBox ibox101))
attribute [irreducible] tree101
private theorem sign_101 : 2*denominator*(computed denominator (FixedTape.midBox ibox101)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox101).gradient k).lo.natAbs ((computed denominator ibox101).gradient k).hi.natAbs : Int)*((ibox101 k).hi-(ibox101 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox101
    (computed denominator ibox101) (computed denominator (FixedTape.midBox ibox101))
    (by decide +kernel)
private theorem midpoint_even_101 : ∀ k, 2 ∣ (ibox101 k).lo+(ibox101 k).hi := by decide +kernel
private theorem accepted_101 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox101) tree101 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox101 midpoint_even_101
  simp only [tree101,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox101,candidate_valid h (FixedTape.midBox ibox101),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox101 106 (FixedTape.rowsAux denominator ibox101 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox101) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_101
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
private noncomputable def tree99 : TapeTree := .split 2 (((190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree100 tree101
attribute [irreducible] tree99
private theorem accepted_99 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox99) tree99 = true := by
  simp only [tree99,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox99 2 (190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) false,decode_split denominator ibox99 2 (190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_100 h,accepted_101 h⟩
private noncomputable def tree98 : TapeTree := .split 3 (((456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree99 tree102
attribute [irreducible] tree98
private theorem accepted_98 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox98) tree98 = true := by
  simp only [tree98,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox98 3 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) false,decode_split denominator ibox98 3 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_99 h,accepted_102 h⟩
private noncomputable def tree97 : TapeTree := .split 2 (((228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree98 tree105
attribute [irreducible] tree97
private theorem accepted_97 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox97) tree97 = true := by
  simp only [tree97,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox97 2 (228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) false,decode_split denominator ibox97 2 (228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_98 h,accepted_105 h⟩
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
private noncomputable def tree95 : TapeTree := .centered (candidateRows ibox95) (candidateRows (FixedTape.midBox ibox95))
attribute [irreducible] tree95
private theorem sign_95 : 2*denominator*(computed denominator (FixedTape.midBox ibox95)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox95).gradient k).lo.natAbs ((computed denominator ibox95).gradient k).hi.natAbs : Int)*((ibox95 k).hi-(ibox95 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox95
    (computed denominator ibox95) (computed denominator (FixedTape.midBox ibox95))
    (by decide +kernel)
private theorem midpoint_even_95 : ∀ k, 2 ∣ (ibox95 k).lo+(ibox95 k).hi := by decide +kernel
private theorem accepted_95 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox95) tree95 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox95 midpoint_even_95
  simp only [tree95,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox95,candidate_valid h (FixedTape.midBox ibox95),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox95 106 (FixedTape.rowsAux denominator ibox95 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox95) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_95
private noncomputable def tree94 : TapeTree := .split 3 (((228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree95 tree96
attribute [irreducible] tree94
private theorem accepted_94 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox94) tree94 = true := by
  simp only [tree94,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox94 3 (228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) false,decode_split denominator ibox94 3 (228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_95 h,accepted_96 h⟩
private noncomputable def tree93 : TapeTree := .centered (candidateRows ibox93) (candidateRows (FixedTape.midBox ibox93))
attribute [irreducible] tree93
private theorem sign_93 : 2*denominator*(computed denominator (FixedTape.midBox ibox93)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox93).gradient k).lo.natAbs ((computed denominator ibox93).gradient k).hi.natAbs : Int)*((ibox93 k).hi-(ibox93 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox93
    (computed denominator ibox93) (computed denominator (FixedTape.midBox ibox93))
    (by decide +kernel)
private theorem midpoint_even_93 : ∀ k, 2 ∣ (ibox93 k).lo+(ibox93 k).hi := by decide +kernel
private theorem accepted_93 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox93) tree93 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox93 midpoint_even_93
  simp only [tree93,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox93,candidate_valid h (FixedTape.midBox ibox93),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox93 106 (FixedTape.rowsAux denominator ibox93 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox93) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_93
private noncomputable def tree92 : TapeTree := .centered (candidateRows ibox92) (candidateRows (FixedTape.midBox ibox92))
attribute [irreducible] tree92
private theorem sign_92 : 2*denominator*(computed denominator (FixedTape.midBox ibox92)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox92).gradient k).lo.natAbs ((computed denominator ibox92).gradient k).hi.natAbs : Int)*((ibox92 k).hi-(ibox92 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox92
    (computed denominator ibox92) (computed denominator (FixedTape.midBox ibox92))
    (by decide +kernel)
private theorem midpoint_even_92 : ∀ k, 2 ∣ (ibox92 k).lo+(ibox92 k).hi := by decide +kernel
private theorem accepted_92 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox92) tree92 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox92 midpoint_even_92
  simp only [tree92,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox92,candidate_valid h (FixedTape.midBox ibox92),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox92 106 (FixedTape.rowsAux denominator ibox92 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox92) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_92
private noncomputable def tree91 : TapeTree := .split 3 (((228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree92 tree93
attribute [irreducible] tree91
private theorem accepted_91 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox91) tree91 = true := by
  simp only [tree91,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox91 3 (228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) false,decode_split denominator ibox91 3 (228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_92 h,accepted_93 h⟩
private noncomputable def tree90 : TapeTree := .split 2 (((266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree91 tree94
attribute [irreducible] tree90
private theorem accepted_90 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox90) tree90 = true := by
  simp only [tree90,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox90 2 (266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 : Int) false,decode_split denominator ibox90 2 (266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_91 h,accepted_94 h⟩
private noncomputable def tree89 : TapeTree := .centered (candidateRows ibox89) (candidateRows (FixedTape.midBox ibox89))
attribute [irreducible] tree89
private theorem sign_89 : 2*denominator*(computed denominator (FixedTape.midBox ibox89)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox89).gradient k).lo.natAbs ((computed denominator ibox89).gradient k).hi.natAbs : Int)*((ibox89 k).hi-(ibox89 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox89
    (computed denominator ibox89) (computed denominator (FixedTape.midBox ibox89))
    (by decide +kernel)
private theorem midpoint_even_89 : ∀ k, 2 ∣ (ibox89 k).lo+(ibox89 k).hi := by decide +kernel
private theorem accepted_89 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox89) tree89 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox89 midpoint_even_89
  simp only [tree89,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox89,candidate_valid h (FixedTape.midBox ibox89),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox89 106 (FixedTape.rowsAux denominator ibox89 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox89) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_89
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
private noncomputable def tree87 : TapeTree := .split 2 (((266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree88 tree89
attribute [irreducible] tree87
private theorem accepted_87 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox87) tree87 = true := by
  simp only [tree87,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox87 2 (266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 : Int) false,decode_split denominator ibox87 2 (266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_88 h,accepted_89 h⟩
private noncomputable def tree86 : TapeTree := .centered (candidateRows ibox86) (candidateRows (FixedTape.midBox ibox86))
attribute [irreducible] tree86
private theorem sign_86 : 2*denominator*(computed denominator (FixedTape.midBox ibox86)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox86).gradient k).lo.natAbs ((computed denominator ibox86).gradient k).hi.natAbs : Int)*((ibox86 k).hi-(ibox86 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox86
    (computed denominator ibox86) (computed denominator (FixedTape.midBox ibox86))
    (by decide +kernel)
private theorem midpoint_even_86 : ∀ k, 2 ∣ (ibox86 k).lo+(ibox86 k).hi := by decide +kernel
private theorem accepted_86 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox86) tree86 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox86 midpoint_even_86
  simp only [tree86,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox86,candidate_valid h (FixedTape.midBox ibox86),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox86 106 (FixedTape.rowsAux denominator ibox86 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox86) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_86
private noncomputable def tree85 : TapeTree := .centered (candidateRows ibox85) (candidateRows (FixedTape.midBox ibox85))
attribute [irreducible] tree85
private theorem sign_85 : 2*denominator*(computed denominator (FixedTape.midBox ibox85)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox85).gradient k).lo.natAbs ((computed denominator ibox85).gradient k).hi.natAbs : Int)*((ibox85 k).hi-(ibox85 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox85
    (computed denominator ibox85) (computed denominator (FixedTape.midBox ibox85))
    (by decide +kernel)
private theorem midpoint_even_85 : ∀ k, 2 ∣ (ibox85 k).lo+(ibox85 k).hi := by decide +kernel
private theorem accepted_85 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox85) tree85 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox85 midpoint_even_85
  simp only [tree85,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox85,candidate_valid h (FixedTape.midBox ibox85),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox85 106 (FixedTape.rowsAux denominator ibox85 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox85) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_85
private noncomputable def tree84 : TapeTree := .split 3 (((38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree85 tree86
attribute [irreducible] tree84
private theorem accepted_84 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox84) tree84 = true := by
  simp only [tree84,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox84 3 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) false,decode_split denominator ibox84 3 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_85 h,accepted_86 h⟩
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
private noncomputable def tree81 : TapeTree := .split 3 (((38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree82 tree83
attribute [irreducible] tree81
private theorem accepted_81 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox81) tree81 = true := by
  simp only [tree81,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox81 3 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) false,decode_split denominator ibox81 3 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_82 h,accepted_83 h⟩
private noncomputable def tree80 : TapeTree := .split 2 (((266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree81 tree84
attribute [irreducible] tree80
private theorem accepted_80 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox80) tree80 = true := by
  simp only [tree80,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox80 2 (266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 : Int) false,decode_split denominator ibox80 2 (266546309309125174009087167906406540481390599954436809368879481968932377853416183648994836296499200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_81 h,accepted_84 h⟩
private noncomputable def tree79 : TapeTree := .split 3 (((76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree80 tree87
attribute [irreducible] tree79
private theorem accepted_79 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox79) tree79 = true := by
  simp only [tree79,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox79 3 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) false,decode_split denominator ibox79 3 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_80 h,accepted_87 h⟩
private noncomputable def tree78 : TapeTree := .split 3 (((152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree79 tree90
attribute [irreducible] tree78
private theorem accepted_78 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox78) tree78 = true := by
  simp only [tree78,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox78 3 (152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) false,decode_split denominator ibox78 3 (152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_79 h,accepted_90 h⟩
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
private noncomputable def tree76 : TapeTree := .centered (candidateRows ibox76) (candidateRows (FixedTape.midBox ibox76))
attribute [irreducible] tree76
private theorem sign_76 : 2*denominator*(computed denominator (FixedTape.midBox ibox76)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox76).gradient k).lo.natAbs ((computed denominator ibox76).gradient k).hi.natAbs : Int)*((ibox76 k).hi-(ibox76 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox76
    (computed denominator ibox76) (computed denominator (FixedTape.midBox ibox76))
    (by decide +kernel)
private theorem midpoint_even_76 : ∀ k, 2 ∣ (ibox76 k).lo+(ibox76 k).hi := by decide +kernel
private theorem accepted_76 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox76) tree76 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox76 midpoint_even_76
  simp only [tree76,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox76,candidate_valid h (FixedTape.midBox ibox76),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox76 106 (FixedTape.rowsAux denominator ibox76 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox76) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_76
private noncomputable def tree75 : TapeTree := .split 3 (((228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree76 tree77
attribute [irreducible] tree75
private theorem accepted_75 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox75) tree75 = true := by
  simp only [tree75,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox75 3 (228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) false,decode_split denominator ibox75 3 (228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_76 h,accepted_77 h⟩
private noncomputable def tree74 : TapeTree := .centered (candidateRows ibox74) (candidateRows (FixedTape.midBox ibox74))
attribute [irreducible] tree74
private theorem sign_74 : 2*denominator*(computed denominator (FixedTape.midBox ibox74)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox74).gradient k).lo.natAbs ((computed denominator ibox74).gradient k).hi.natAbs : Int)*((ibox74 k).hi-(ibox74 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox74
    (computed denominator ibox74) (computed denominator (FixedTape.midBox ibox74))
    (by decide +kernel)
private theorem midpoint_even_74 : ∀ k, 2 ∣ (ibox74 k).lo+(ibox74 k).hi := by decide +kernel
private theorem accepted_74 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox74) tree74 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox74 midpoint_even_74
  simp only [tree74,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox74,candidate_valid h (FixedTape.midBox ibox74),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox74 106 (FixedTape.rowsAux denominator ibox74 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox74) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_74
private noncomputable def tree73 : TapeTree := .centered (candidateRows ibox73) (candidateRows (FixedTape.midBox ibox73))
attribute [irreducible] tree73
private theorem sign_73 : 2*denominator*(computed denominator (FixedTape.midBox ibox73)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox73).gradient k).lo.natAbs ((computed denominator ibox73).gradient k).hi.natAbs : Int)*((ibox73 k).hi-(ibox73 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox73
    (computed denominator ibox73) (computed denominator (FixedTape.midBox ibox73))
    (by decide +kernel)
private theorem midpoint_even_73 : ∀ k, 2 ∣ (ibox73 k).lo+(ibox73 k).hi := by decide +kernel
private theorem accepted_73 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox73) tree73 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox73 midpoint_even_73
  simp only [tree73,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox73,candidate_valid h (FixedTape.midBox ibox73),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox73 106 (FixedTape.rowsAux denominator ibox73 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox73) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_73
private noncomputable def tree72 : TapeTree := .split 3 (((228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree73 tree74
attribute [irreducible] tree72
private theorem accepted_72 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox72) tree72 = true := by
  simp only [tree72,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox72 3 (228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) false,decode_split denominator ibox72 3 (228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_73 h,accepted_74 h⟩
private noncomputable def tree71 : TapeTree := .split 2 (((190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree72 tree75
attribute [irreducible] tree71
private theorem accepted_71 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox71) tree71 = true := by
  simp only [tree71,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox71 2 (190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) false,decode_split denominator ibox71 2 (190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_72 h,accepted_75 h⟩
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
private noncomputable def tree68 : TapeTree := .centered (candidateRows ibox68) (candidateRows (FixedTape.midBox ibox68))
attribute [irreducible] tree68
private theorem sign_68 : 2*denominator*(computed denominator (FixedTape.midBox ibox68)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox68).gradient k).lo.natAbs ((computed denominator ibox68).gradient k).hi.natAbs : Int)*((ibox68 k).hi-(ibox68 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox68
    (computed denominator ibox68) (computed denominator (FixedTape.midBox ibox68))
    (by decide +kernel)
private theorem midpoint_even_68 : ∀ k, 2 ∣ (ibox68 k).lo+(ibox68 k).hi := by decide +kernel
private theorem accepted_68 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox68) tree68 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox68 midpoint_even_68
  simp only [tree68,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox68,candidate_valid h (FixedTape.midBox ibox68),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox68 106 (FixedTape.rowsAux denominator ibox68 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox68) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_68
private noncomputable def tree67 : TapeTree := .split 2 (((209429243028598351007139917640747996092521185678486064504119592975589725456255572867067371375820800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree68 tree69
attribute [irreducible] tree67
private theorem accepted_67 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox67) tree67 = true := by
  simp only [tree67,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox67 2 (209429243028598351007139917640747996092521185678486064504119592975589725456255572867067371375820800000000000000000000000 : Int) false,decode_split denominator ibox67 2 (209429243028598351007139917640747996092521185678486064504119592975589725456255572867067371375820800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_68 h,accepted_69 h⟩
private noncomputable def tree66 : TapeTree := .split 3 (((76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree67 tree70
attribute [irreducible] tree66
private theorem accepted_66 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox66) tree66 = true := by
  simp only [tree66,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox66 3 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) false,decode_split denominator ibox66 3 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_67 h,accepted_70 h⟩
private noncomputable def tree65 : TapeTree := .centered (candidateRows ibox65) (candidateRows (FixedTape.midBox ibox65))
attribute [irreducible] tree65
private theorem sign_65 : 2*denominator*(computed denominator (FixedTape.midBox ibox65)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox65).gradient k).lo.natAbs ((computed denominator ibox65).gradient k).hi.natAbs : Int)*((ibox65 k).hi-(ibox65 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox65
    (computed denominator ibox65) (computed denominator (FixedTape.midBox ibox65))
    (by decide +kernel)
private theorem midpoint_even_65 : ∀ k, 2 ∣ (ibox65 k).lo+(ibox65 k).hi := by decide +kernel
private theorem accepted_65 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox65) tree65 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox65 midpoint_even_65
  simp only [tree65,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox65,candidate_valid h (FixedTape.midBox ibox65),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox65 106 (FixedTape.rowsAux denominator ibox65 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox65) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_65
private noncomputable def tree64 : TapeTree := .centered (candidateRows ibox64) (candidateRows (FixedTape.midBox ibox64))
attribute [irreducible] tree64
private theorem sign_64 : 2*denominator*(computed denominator (FixedTape.midBox ibox64)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox64).gradient k).lo.natAbs ((computed denominator ibox64).gradient k).hi.natAbs : Int)*((ibox64 k).hi-(ibox64 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox64
    (computed denominator ibox64) (computed denominator (FixedTape.midBox ibox64))
    (by decide +kernel)
private theorem midpoint_even_64 : ∀ k, 2 ∣ (ibox64 k).lo+(ibox64 k).hi := by decide +kernel
private theorem accepted_64 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox64) tree64 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox64 midpoint_even_64
  simp only [tree64,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox64,candidate_valid h (FixedTape.midBox ibox64),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox64 106 (FixedTape.rowsAux denominator ibox64 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox64) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_64
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
private noncomputable def tree62 : TapeTree := .split 2 (((171351198841580469005841750796975633166608242827852234594279666980027957191481832345782394762035200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree63 tree64
attribute [irreducible] tree62
private theorem accepted_62 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox62) tree62 = true := by
  simp only [tree62,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox62 2 (171351198841580469005841750796975633166608242827852234594279666980027957191481832345782394762035200000000000000000000000 : Int) false,decode_split denominator ibox62 2 (171351198841580469005841750796975633166608242827852234594279666980027957191481832345782394762035200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_63 h,accepted_64 h⟩
private noncomputable def tree61 : TapeTree := .split 3 (((76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree62 tree65
attribute [irreducible] tree61
private theorem accepted_61 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox61) tree61 = true := by
  simp only [tree61,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox61 3 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) false,decode_split denominator ibox61 3 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_62 h,accepted_65 h⟩
private noncomputable def tree60 : TapeTree := .split 2 (((190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree61 tree66
attribute [irreducible] tree60
private theorem accepted_60 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox60) tree60 = true := by
  simp only [tree60,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox60 2 (190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) false,decode_split denominator ibox60 2 (190390220935089410006490834218861814629564714253169149549199629977808841323868702606424883068928000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_61 h,accepted_66 h⟩
private noncomputable def tree59 : TapeTree := .split 3 (((152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree60 tree71
attribute [irreducible] tree59
private theorem accepted_59 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox59) tree59 = true := by
  simp only [tree59,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox59 3 (152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) false,decode_split denominator ibox59 3 (152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_60 h,accepted_71 h⟩
private noncomputable def tree58 : TapeTree := .split 2 (((228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree59 tree78
attribute [irreducible] tree58
private theorem accepted_58 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox58) tree58 = true := by
  simp only [tree58,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox58 2 (228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) false,decode_split denominator ibox58 2 (228468265122107292007789001062634177555477657103802979459039555973370609588642443127709859682713600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_59 h,accepted_78 h⟩
private noncomputable def tree57 : TapeTree := .split 3 (((304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree58 tree97
attribute [irreducible] tree57
private theorem accepted_57 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox57) tree57 = true := by
  simp only [tree57,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox57 3 (304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) false,decode_split denominator ibox57 3 (304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_58 h,accepted_97 h⟩
private noncomputable def tree56 : TapeTree := .centered (candidateRows ibox56) (candidateRows (FixedTape.midBox ibox56))
attribute [irreducible] tree56
private theorem sign_56 : 2*denominator*(computed denominator (FixedTape.midBox ibox56)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox56).gradient k).lo.natAbs ((computed denominator ibox56).gradient k).hi.natAbs : Int)*((ibox56 k).hi-(ibox56 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox56
    (computed denominator ibox56) (computed denominator (FixedTape.midBox ibox56))
    (by decide +kernel)
private theorem midpoint_even_56 : ∀ k, 2 ∣ (ibox56 k).lo+(ibox56 k).hi := by decide +kernel
private theorem accepted_56 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox56) tree56 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox56 midpoint_even_56
  simp only [tree56,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox56,candidate_valid h (FixedTape.midBox ibox56),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox56 106 (FixedTape.rowsAux denominator ibox56 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox56) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_56
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
private noncomputable def tree54 : TapeTree := .split 2 (((114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree55 tree56
attribute [irreducible] tree54
private theorem accepted_54 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox54) tree54 = true := by
  simp only [tree54,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox54 2 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) false,decode_split denominator ibox54 2 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_55 h,accepted_56 h⟩
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
private noncomputable def tree51 : TapeTree := .split 2 (((114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree52 tree53
attribute [irreducible] tree51
private theorem accepted_51 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox51) tree51 = true := by
  simp only [tree51,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox51 2 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) false,decode_split denominator ibox51 2 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_52 h,accepted_53 h⟩
private noncomputable def tree50 : TapeTree := .split 3 (((456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree51 tree54
attribute [irreducible] tree50
private theorem accepted_50 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox50) tree50 = true := by
  simp only [tree50,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox50 3 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) false,decode_split denominator ibox50 3 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_51 h,accepted_54 h⟩
private noncomputable def tree49 : TapeTree := .centered (candidateRows ibox49) (candidateRows (FixedTape.midBox ibox49))
attribute [irreducible] tree49
private theorem sign_49 : 2*denominator*(computed denominator (FixedTape.midBox ibox49)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox49).gradient k).lo.natAbs ((computed denominator ibox49).gradient k).hi.natAbs : Int)*((ibox49 k).hi-(ibox49 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox49
    (computed denominator ibox49) (computed denominator (FixedTape.midBox ibox49))
    (by decide +kernel)
private theorem midpoint_even_49 : ∀ k, 2 ∣ (ibox49 k).lo+(ibox49 k).hi := by decide +kernel
private theorem accepted_49 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox49) tree49 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox49 midpoint_even_49
  simp only [tree49,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox49,candidate_valid h (FixedTape.midBox ibox49),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox49 106 (FixedTape.rowsAux denominator ibox49 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox49) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_49
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
private noncomputable def tree47 : TapeTree := .split 3 (((456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree48 tree49
attribute [irreducible] tree47
private theorem accepted_47 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox47) tree47 = true := by
  simp only [tree47,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox47 3 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) false,decode_split denominator ibox47 3 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_48 h,accepted_49 h⟩
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
private noncomputable def tree45 : TapeTree := .split 2 (((38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree46 tree47
attribute [irreducible] tree45
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox45 2 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) false,decode_split denominator ibox45 2 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_46 h,accepted_47 h⟩
private noncomputable def tree44 : TapeTree := .split 2 (((76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree45 tree50
attribute [irreducible] tree44
private theorem accepted_44 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox44) tree44 = true := by
  simp only [tree44,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox44 2 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) false,decode_split denominator ibox44 2 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_45 h,accepted_50 h⟩
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
private noncomputable def tree41 : TapeTree := .split 2 (((114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree42 tree43
attribute [irreducible] tree41
private theorem accepted_41 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox41) tree41 = true := by
  simp only [tree41,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox41 2 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) false,decode_split denominator ibox41 2 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_42 h,accepted_43 h⟩
private noncomputable def tree40 : TapeTree := .centered (candidateRows ibox40) (candidateRows (FixedTape.midBox ibox40))
attribute [irreducible] tree40
private theorem sign_40 : 2*denominator*(computed denominator (FixedTape.midBox ibox40)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox40).gradient k).lo.natAbs ((computed denominator ibox40).gradient k).hi.natAbs : Int)*((ibox40 k).hi-(ibox40 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox40
    (computed denominator ibox40) (computed denominator (FixedTape.midBox ibox40))
    (by decide +kernel)
private theorem midpoint_even_40 : ∀ k, 2 ∣ (ibox40 k).lo+(ibox40 k).hi := by decide +kernel
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox40 midpoint_even_40
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox40,candidate_valid h (FixedTape.midBox ibox40),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox40 106 (FixedTape.rowsAux denominator ibox40 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox40) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_40
private noncomputable def tree39 : TapeTree := .centered (candidateRows ibox39) (candidateRows (FixedTape.midBox ibox39))
attribute [irreducible] tree39
private theorem sign_39 : 2*denominator*(computed denominator (FixedTape.midBox ibox39)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox39).gradient k).lo.natAbs ((computed denominator ibox39).gradient k).hi.natAbs : Int)*((ibox39 k).hi-(ibox39 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox39
    (computed denominator ibox39) (computed denominator (FixedTape.midBox ibox39))
    (by decide +kernel)
private theorem midpoint_even_39 : ∀ k, 2 ∣ (ibox39 k).lo+(ibox39 k).hi := by decide +kernel
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox39 midpoint_even_39
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox39,candidate_valid h (FixedTape.midBox ibox39),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox39 106 (FixedTape.rowsAux denominator ibox39 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox39) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_39
private noncomputable def tree38 : TapeTree := .centered (candidateRows ibox38) (candidateRows (FixedTape.midBox ibox38))
attribute [irreducible] tree38
private theorem sign_38 : 2*denominator*(computed denominator (FixedTape.midBox ibox38)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox38).gradient k).lo.natAbs ((computed denominator ibox38).gradient k).hi.natAbs : Int)*((ibox38 k).hi-(ibox38 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox38
    (computed denominator ibox38) (computed denominator (FixedTape.midBox ibox38))
    (by decide +kernel)
private theorem midpoint_even_38 : ∀ k, 2 ∣ (ibox38 k).lo+(ibox38 k).hi := by decide +kernel
private theorem accepted_38 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox38) tree38 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox38 midpoint_even_38
  simp only [tree38,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox38,candidate_valid h (FixedTape.midBox ibox38),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox38 106 (FixedTape.rowsAux denominator ibox38 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox38) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_38
private noncomputable def tree37 : TapeTree := .split 2 (((133273154654562587004543583953203270240695299977218404684439740984466188926708091824497418148249600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree38 tree39
attribute [irreducible] tree37
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox37 2 (133273154654562587004543583953203270240695299977218404684439740984466188926708091824497418148249600000000000000000000000 : Int) false,decode_split denominator ibox37 2 (133273154654562587004543583953203270240695299977218404684439740984466188926708091824497418148249600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_38 h,accepted_39 h⟩
private noncomputable def tree36 : TapeTree := .split 3 (((76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree37 tree40
attribute [irreducible] tree36
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox36 3 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) false,decode_split denominator ibox36 3 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_37 h,accepted_40 h⟩
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
private noncomputable def tree34 : TapeTree := .centered (candidateRows ibox34) (candidateRows (FixedTape.midBox ibox34))
attribute [irreducible] tree34
private theorem sign_34 : 2*denominator*(computed denominator (FixedTape.midBox ibox34)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox34).gradient k).lo.natAbs ((computed denominator ibox34).gradient k).hi.natAbs : Int)*((ibox34 k).hi-(ibox34 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox34
    (computed denominator ibox34) (computed denominator (FixedTape.midBox ibox34))
    (by decide +kernel)
private theorem midpoint_even_34 : ∀ k, 2 ∣ (ibox34 k).lo+(ibox34 k).hi := by decide +kernel
private theorem accepted_34 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox34) tree34 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox34 midpoint_even_34
  simp only [tree34,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox34,candidate_valid h (FixedTape.midBox ibox34),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox34 106 (FixedTape.rowsAux denominator ibox34 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox34) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_34
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
private noncomputable def tree32 : TapeTree := .split 2 (((95195110467544705003245417109430907314782357126584574774599814988904420661934351303212441534464000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree33 tree34
attribute [irreducible] tree32
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox32 2 (95195110467544705003245417109430907314782357126584574774599814988904420661934351303212441534464000000000000000000000000 : Int) false,decode_split denominator ibox32 2 (95195110467544705003245417109430907314782357126584574774599814988904420661934351303212441534464000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_33 h,accepted_34 h⟩
private noncomputable def tree31 : TapeTree := .split 3 (((76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree32 tree35
attribute [irreducible] tree31
private theorem accepted_31 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox31) tree31 = true := by
  simp only [tree31,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox31 3 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) false,decode_split denominator ibox31 3 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_32 h,accepted_35 h⟩
private noncomputable def tree30 : TapeTree := .split 2 (((114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree31 tree36
attribute [irreducible] tree30
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox30 2 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) false,decode_split denominator ibox30 2 (114234132561053646003894500531317088777738828551901489729519777986685304794321221563854929841356800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_31 h,accepted_36 h⟩
private noncomputable def tree29 : TapeTree := .split 3 (((152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree30 tree41
attribute [irreducible] tree29
private theorem accepted_29 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox29) tree29 = true := by
  simp only [tree29,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox29 3 (152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) false,decode_split denominator ibox29 3 (152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_30 h,accepted_41 h⟩
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
private noncomputable def tree26 : TapeTree := .split 2 (((38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree27 tree28
attribute [irreducible] tree26
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox26 2 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) false,decode_split denominator ibox26 2 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_27 h,accepted_28 h⟩
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
private noncomputable def tree23 : TapeTree := .split 3 (((76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree24 tree25
attribute [irreducible] tree23
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox23 3 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) false,decode_split denominator ibox23 3 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_24 h,accepted_25 h⟩
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
private noncomputable def tree21 : TapeTree := .face 3 false (candidateRows ibox21) tree22
attribute [irreducible] tree21
private theorem sign_21 : ((computed denominator ibox21).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox21,?_,accepted_22 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox21)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox21).gradient 3).hi) denominator_positive).1 sign_21
private noncomputable def tree20 : TapeTree := .split 2 (((38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree21 tree23
attribute [irreducible] tree20
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox20 2 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) false,decode_split denominator ibox20 2 (38078044187017882001298166843772362925912942850633829909839925995561768264773740521284976613785600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_21 h,accepted_23 h⟩
private noncomputable def tree19 : TapeTree := .split 3 (((152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree26
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 3 (152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) false,decode_split denominator ibox19 3 (152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_20 h,accepted_26 h⟩
private noncomputable def tree18 : TapeTree := .split 2 (((76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree19 tree29
attribute [irreducible] tree18
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox18 2 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) false,decode_split denominator ibox18 2 (76156088374035764002596333687544725851825885701267659819679851991123536529547481042569953227571200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_19 h,accepted_29 h⟩
private noncomputable def tree17 : TapeTree := .split 3 (((304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree18 tree44
attribute [irreducible] tree17
private theorem accepted_17 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox17) tree17 = true := by
  simp only [tree17,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox17 3 (304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) false,decode_split denominator ibox17 3 (304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_18 h,accepted_44 h⟩
private noncomputable def tree16 : TapeTree := .split 2 (((152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree57
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 2 (152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) false,decode_split denominator ibox16 2 (152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_17 h,accepted_57 h⟩
private noncomputable def tree15 : TapeTree := .split 2 (((304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree16 tree112
attribute [irreducible] tree15
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox15 2 (304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) false,decode_split denominator ibox15 2 (304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_16 h,accepted_112 h⟩
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
private noncomputable def tree11 : TapeTree := .split 2 (((456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree12 tree13
attribute [irreducible] tree11
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox11 2 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) false,decode_split denominator ibox11 2 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) true]
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
private noncomputable def tree8 : TapeTree := .split 2 (((152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree9 tree10
attribute [irreducible] tree8
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox8 2 (152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) false,decode_split denominator ibox8 2 (152312176748071528005192667375089451703651771402535319639359703982247073059094962085139906455142400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_9 h,accepted_10 h⟩
private noncomputable def tree7 : TapeTree := .split 2 (((304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree8 tree11
attribute [irreducible] tree7
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox7 2 (304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) false,decode_split denominator ibox7 2 (304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) true]
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
private noncomputable def tree5 : TapeTree := .split 1 (((456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree6 tree14
attribute [irreducible] tree5
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox5 1 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) false,decode_split denominator ibox5 1 (456936530244214584015578002125268355110955314207605958918079111946741219177284886255419719365427200000000000000000000000 : Int) true]
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
private noncomputable def tree2 : TapeTree := .split 2 (((304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree4
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 2 (304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) false,decode_split denominator ibox2 2 (304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) true]
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
private noncomputable def tree0 : TapeTree := .split 1 (((304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree1 tree5
attribute [irreducible] tree0
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox0 1 (304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) false,decode_split denominator ibox0 1 (304624353496143056010385334750178903407303542805070639278719407964494146118189924170279812910284800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_1 h,accepted_5 h⟩
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (1/2 : ℚ) (2552083333333333/5000000000000000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 106 = e112 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (1/2 : ℚ) (2552083333333333/5000000000000000 : ℚ)) x → eval e112 x ≤ 0 := by
  have hb := h.child_4 tape 106 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell70_low_internal

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell70_low_internal
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((1/2 : ℚ) : ℝ) < p ∧ p ≤ ((2552083333333333/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 70 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 70 p)
    (hk0 : ((2552083333333333/5000000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((1/2 : ℚ) : ℝ))
    (hk1 : ((2552083333333333/5000000000000000 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((1/2 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell70_low_internal.cell_bound h.child_8 h.child_9 (Cell70_low_internal.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell70_low_internal
