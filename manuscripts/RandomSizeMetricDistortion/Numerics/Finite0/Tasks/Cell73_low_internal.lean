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
namespace Cell73_low_internal
private noncomputable def qValues : Fin 4 → ℚ := ![(6016250411964745401961105207242503323/7531037802584344267842282209888214501 : ℚ),(9817816783973409861612500000000000000/7531037802584344267842282209888214501 : ℚ),(26795592110003909359885749303687375050/9929124871906057746241809384157060431 : ℚ),(-16389539581248857310605000000000000000/9929124871906057746241809384157060431 : ℚ)]
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
    priceLambda 73 p = ((6016250411964745401961105207242503323/7531037802584344267842282209888214501 : ℝ)+(9817816783973409861612500000000000000/7531037802584344267842282209888214501 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell73,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 73 p = (((26795592110003909359885749303687375050/9929124871906057746241809384157060431 : ℝ)+(-16389539581248857310605000000000000000/9929124871906057746241809384157060431 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell73,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e112 x = (x 0*(1-x 0))*(aPoint x+priceLambda 73 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 73 (x 0)*psiStar (rPoint x)+(0)-(0)) := by
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
    (hL : lambdaStar (x 0) = priceLambda 73 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 73 (x 0)) :
    (1)*eval e112 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,if_pos hA,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (17/32 : ℚ) (2708333333333333/5000000000000000 : ℚ)) x → eval e112 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((17/32 : ℚ) : ℝ) < p ∧ p ≤ ((2708333333333333/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 73 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 73 p)
    (hk0 : ((2708333333333333/5000000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((17/32 : ℚ) : ℝ))
    (hk1 : ((2708333333333333/5000000000000000 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((17/32 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h3 (17/32 : ℚ) (2708333333333333/5000000000000000 : ℚ) ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ) p a A r hpcell hk0 hk1 hr ha hap hpA hAr
  have hcut : ¬(((2708333333333333/5000000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ)) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint,if_neg hcut] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint,if_neg hcut] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint,if_neg hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 73 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 73 (x 0) := by simpa only [hxp] using hT
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
.const (6016250411964745401961105207242503323/7531037802584344267842282209888214501 : ℚ),
.const (9817816783973409861612500000000000000/7531037802584344267842282209888214501 : ℚ),
.mul 74 1,
.add 73 75,
.const (26795592110003909359885749303687375050/9929124871906057746241809384157060431 : ℚ),
.const (-16389539581248857310605000000000000000/9929124871906057746241809384157060431 : ℚ),
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
private noncomputable def ssaQVals : Fin 15 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(6016250411964745401961105207242503323/7531037802584344267842282209888214501 : ℚ),(9817816783973409861612500000000000000/7531037802584344267842282209888214501 : ℚ),(26795592110003909359885749303687375050/9929124871906057746241809384157060431 : ℚ),(-16389539581248857310605000000000000000/9929124871906057746241809384157060431 : ℚ),(-145513/100000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
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
private noncomputable def denominator : Int := 34097312335064048142535968322539167152744509631641384850441178084442934915649086478358051343564800000000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨18114197178002775575722233171348932549895520741809485701796875857360309173938577191627714776268800000000000000000000000,18469377514826357137386160503772172705338721214527939944354996019647599716564716212914950101158501442796577095680000000⟩,⟨0,34097312335064048142535968322539167152744509631641384850441178084442934915649086478358051343564800000000000000000000000⟩,⟨0,34097312335064048142535968322539167152744509631641384850441178084442934915649086478358051343564800000000000000000000000⟩,⟨0,34097312335064048142535968322539167152744509631641384850441178084442934915649086478358051343564800000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := splitI ibox0 1 17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 1 true
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox0 1 17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 true
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := faceI ibox4 1 true
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox5 2 17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 false
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox5 2 17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 true
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox3 1 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := faceI ibox8 1 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox9 2 17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 false
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox10 2 8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 false
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox11 2 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 false
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox12 3 17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 false
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox13 2 2131082020941503008908498020158697947046531851977586553152573630277683432228067904897378208972800000000000000000000000 false
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox14 3 8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 false
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox14 3 8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 true
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox13 2 2131082020941503008908498020158697947046531851977586553152573630277683432228067904897378208972800000000000000000000000 true
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox17 3 8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 false
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox17 3 8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox12 3 17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 true
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox20 2 2131082020941503008908498020158697947046531851977586553152573630277683432228067904897378208972800000000000000000000000 false
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox20 2 2131082020941503008908498020158697947046531851977586553152573630277683432228067904897378208972800000000000000000000000 true
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox22 3 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 false
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox22 3 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 true
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox11 2 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 true
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox25 3 17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 false
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox26 2 6393246062824509026725494060476093841139595555932759659457720890833050296684203714692134626918400000000000000000000000 false
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox27 3 8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 false
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox27 3 8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 true
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox26 2 6393246062824509026725494060476093841139595555932759659457720890833050296684203714692134626918400000000000000000000000 true
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox30 3 8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 false
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox31 2 7458787073295260531179743070555442814662861481921552936034007705971892012798237667140823731404800000000000000000000000 false
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox31 2 7458787073295260531179743070555442814662861481921552936034007705971892012798237667140823731404800000000000000000000000 true
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox30 3 8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 true
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox25 3 17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 true
private noncomputable def ibox36 : Fin 4 → FixedTape.I := splitI ibox35 2 6393246062824509026725494060476093841139595555932759659457720890833050296684203714692134626918400000000000000000000000 false
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox36 3 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 false
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox36 3 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 true
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox35 2 6393246062824509026725494060476093841139595555932759659457720890833050296684203714692134626918400000000000000000000000 true
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox39 3 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 false
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox39 3 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 true
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox10 2 8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 true
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox42 3 17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 false
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox43 2 12786492125649018053450988120952187682279191111865519318915441781666100593368407429384269253836800000000000000000000000 false
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox44 3 8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 false
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox45 2 10655410104707515044542490100793489735232659259887932765762868151388417161140339524486891044864000000000000000000000000 false
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox46 3 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 false
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox46 3 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 true
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox45 2 10655410104707515044542490100793489735232659259887932765762868151388417161140339524486891044864000000000000000000000000 true
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox49 3 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 false
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox49 3 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 true
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox44 3 8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 true
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox52 2 10655410104707515044542490100793489735232659259887932765762868151388417161140339524486891044864000000000000000000000000 false
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox52 2 10655410104707515044542490100793489735232659259887932765762868151388417161140339524486891044864000000000000000000000000 true
private noncomputable def ibox55 : Fin 4 → FixedTape.I := splitI ibox54 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox54 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox43 2 12786492125649018053450988120952187682279191111865519318915441781666100593368407429384269253836800000000000000000000000 true
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox57 3 8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 false
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox58 2 14917574146590521062359486141110885629325722963843105872068015411943784025596475334281647462809600000000000000000000000 false
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox59 3 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 false
private noncomputable def ibox61 : Fin 4 → FixedTape.I := splitI ibox59 3 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 true
private noncomputable def ibox62 : Fin 4 → FixedTape.I := splitI ibox58 2 14917574146590521062359486141110885629325722963843105872068015411943784025596475334281647462809600000000000000000000000 true
private noncomputable def ibox63 : Fin 4 → FixedTape.I := splitI ibox62 3 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 false
private noncomputable def ibox64 : Fin 4 → FixedTape.I := splitI ibox62 3 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 true
private noncomputable def ibox65 : Fin 4 → FixedTape.I := splitI ibox57 3 8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 true
private noncomputable def ibox66 : Fin 4 → FixedTape.I := splitI ibox65 2 14917574146590521062359486141110885629325722963843105872068015411943784025596475334281647462809600000000000000000000000 false
private noncomputable def ibox67 : Fin 4 → FixedTape.I := splitI ibox66 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox68 : Fin 4 → FixedTape.I := splitI ibox66 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox69 : Fin 4 → FixedTape.I := splitI ibox65 2 14917574146590521062359486141110885629325722963843105872068015411943784025596475334281647462809600000000000000000000000 true
private noncomputable def ibox70 : Fin 4 → FixedTape.I := splitI ibox69 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox71 : Fin 4 → FixedTape.I := splitI ibox69 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox72 : Fin 4 → FixedTape.I := splitI ibox42 3 17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 true
private noncomputable def ibox73 : Fin 4 → FixedTape.I := splitI ibox72 2 12786492125649018053450988120952187682279191111865519318915441781666100593368407429384269253836800000000000000000000000 false
private noncomputable def ibox74 : Fin 4 → FixedTape.I := splitI ibox73 2 10655410104707515044542490100793489735232659259887932765762868151388417161140339524486891044864000000000000000000000000 false
private noncomputable def ibox75 : Fin 4 → FixedTape.I := splitI ibox74 3 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 false
private noncomputable def ibox76 : Fin 4 → FixedTape.I := splitI ibox74 3 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 true
private noncomputable def ibox77 : Fin 4 → FixedTape.I := splitI ibox73 2 10655410104707515044542490100793489735232659259887932765762868151388417161140339524486891044864000000000000000000000000 true
private noncomputable def ibox78 : Fin 4 → FixedTape.I := splitI ibox77 3 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 false
private noncomputable def ibox79 : Fin 4 → FixedTape.I := splitI ibox77 3 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 true
private noncomputable def ibox80 : Fin 4 → FixedTape.I := splitI ibox72 2 12786492125649018053450988120952187682279191111865519318915441781666100593368407429384269253836800000000000000000000000 true
private noncomputable def ibox81 : Fin 4 → FixedTape.I := splitI ibox80 3 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 false
private noncomputable def ibox82 : Fin 4 → FixedTape.I := splitI ibox81 2 14917574146590521062359486141110885629325722963843105872068015411943784025596475334281647462809600000000000000000000000 false
private noncomputable def ibox83 : Fin 4 → FixedTape.I := splitI ibox82 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox84 : Fin 4 → FixedTape.I := splitI ibox82 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox85 : Fin 4 → FixedTape.I := splitI ibox81 2 14917574146590521062359486141110885629325722963843105872068015411943784025596475334281647462809600000000000000000000000 true
private noncomputable def ibox86 : Fin 4 → FixedTape.I := splitI ibox85 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox87 : Fin 4 → FixedTape.I := splitI ibox85 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox88 : Fin 4 → FixedTape.I := splitI ibox80 3 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 true
private noncomputable def ibox89 : Fin 4 → FixedTape.I := splitI ibox88 2 14917574146590521062359486141110885629325722963843105872068015411943784025596475334281647462809600000000000000000000000 false
private noncomputable def ibox90 : Fin 4 → FixedTape.I := splitI ibox88 2 14917574146590521062359486141110885629325722963843105872068015411943784025596475334281647462809600000000000000000000000 true
private noncomputable def ibox91 : Fin 4 → FixedTape.I := splitI ibox9 2 17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 true
private noncomputable def ibox92 : Fin 4 → FixedTape.I := splitI ibox91 2 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 false
private noncomputable def ibox93 : Fin 4 → FixedTape.I := splitI ibox92 3 17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 false
private noncomputable def ibox94 : Fin 4 → FixedTape.I := splitI ibox93 2 21310820209415030089084980201586979470465318519775865531525736302776834322280679048973782089728000000000000000000000000 false
private noncomputable def ibox95 : Fin 4 → FixedTape.I := splitI ibox94 3 8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 false
private noncomputable def ibox96 : Fin 4 → FixedTape.I := splitI ibox95 2 19179738188473527080176482181428281523418786667798278978373162672499150890052611144076403880755200000000000000000000000 false
private noncomputable def ibox97 : Fin 4 → FixedTape.I := splitI ibox96 3 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 false
private noncomputable def ibox98 : Fin 4 → FixedTape.I := splitI ibox96 3 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 true
private noncomputable def ibox99 : Fin 4 → FixedTape.I := splitI ibox95 2 19179738188473527080176482181428281523418786667798278978373162672499150890052611144076403880755200000000000000000000000 true
private noncomputable def ibox100 : Fin 4 → FixedTape.I := splitI ibox99 3 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 false
private noncomputable def ibox101 : Fin 4 → FixedTape.I := splitI ibox100 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox102 : Fin 4 → FixedTape.I := splitI ibox100 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox103 : Fin 4 → FixedTape.I := splitI ibox99 3 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 true
private noncomputable def ibox104 : Fin 4 → FixedTape.I := splitI ibox94 3 8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 true
private noncomputable def ibox105 : Fin 4 → FixedTape.I := splitI ibox104 2 19179738188473527080176482181428281523418786667798278978373162672499150890052611144076403880755200000000000000000000000 false
private noncomputable def ibox106 : Fin 4 → FixedTape.I := splitI ibox105 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox107 : Fin 4 → FixedTape.I := splitI ibox105 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox108 : Fin 4 → FixedTape.I := splitI ibox104 2 19179738188473527080176482181428281523418786667798278978373162672499150890052611144076403880755200000000000000000000000 true
private noncomputable def ibox109 : Fin 4 → FixedTape.I := splitI ibox108 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox110 : Fin 4 → FixedTape.I := splitI ibox108 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox111 : Fin 4 → FixedTape.I := splitI ibox93 2 21310820209415030089084980201586979470465318519775865531525736302776834322280679048973782089728000000000000000000000000 true
private noncomputable def ibox112 : Fin 4 → FixedTape.I := splitI ibox111 3 8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 false
private noncomputable def ibox113 : Fin 4 → FixedTape.I := splitI ibox112 2 23441902230356533097993478221745677417511850371753452084678309933054517754508746953871160298700800000000000000000000000 false
private noncomputable def ibox114 : Fin 4 → FixedTape.I := splitI ibox113 3 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 false
private noncomputable def ibox115 : Fin 4 → FixedTape.I := splitI ibox114 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox116 : Fin 4 → FixedTape.I := splitI ibox114 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox117 : Fin 4 → FixedTape.I := splitI ibox113 3 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 true
private noncomputable def ibox118 : Fin 4 → FixedTape.I := splitI ibox112 2 23441902230356533097993478221745677417511850371753452084678309933054517754508746953871160298700800000000000000000000000 true
private noncomputable def ibox119 : Fin 4 → FixedTape.I := splitI ibox118 3 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 false
private noncomputable def ibox120 : Fin 4 → FixedTape.I := splitI ibox119 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox121 : Fin 4 → FixedTape.I := splitI ibox119 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox122 : Fin 4 → FixedTape.I := splitI ibox118 3 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 true
private noncomputable def ibox123 : Fin 4 → FixedTape.I := splitI ibox122 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox124 : Fin 4 → FixedTape.I := splitI ibox122 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox125 : Fin 4 → FixedTape.I := splitI ibox111 3 8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 true
private noncomputable def ibox126 : Fin 4 → FixedTape.I := splitI ibox125 2 23441902230356533097993478221745677417511850371753452084678309933054517754508746953871160298700800000000000000000000000 false
private noncomputable def ibox127 : Fin 4 → FixedTape.I := splitI ibox126 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox128 : Fin 4 → FixedTape.I := splitI ibox126 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox129 : Fin 4 → FixedTape.I := splitI ibox125 2 23441902230356533097993478221745677417511850371753452084678309933054517754508746953871160298700800000000000000000000000 true
private noncomputable def ibox130 : Fin 4 → FixedTape.I := splitI ibox129 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox131 : Fin 4 → FixedTape.I := splitI ibox129 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox132 : Fin 4 → FixedTape.I := splitI ibox92 3 17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 true
private noncomputable def ibox133 : Fin 4 → FixedTape.I := splitI ibox132 2 21310820209415030089084980201586979470465318519775865531525736302776834322280679048973782089728000000000000000000000000 false
private noncomputable def ibox134 : Fin 4 → FixedTape.I := splitI ibox133 3 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 false
private noncomputable def ibox135 : Fin 4 → FixedTape.I := splitI ibox134 2 19179738188473527080176482181428281523418786667798278978373162672499150890052611144076403880755200000000000000000000000 false
private noncomputable def ibox136 : Fin 4 → FixedTape.I := splitI ibox135 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox137 : Fin 4 → FixedTape.I := splitI ibox135 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox138 : Fin 4 → FixedTape.I := splitI ibox134 2 19179738188473527080176482181428281523418786667798278978373162672499150890052611144076403880755200000000000000000000000 true
private noncomputable def ibox139 : Fin 4 → FixedTape.I := splitI ibox138 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox140 : Fin 4 → FixedTape.I := splitI ibox138 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox141 : Fin 4 → FixedTape.I := splitI ibox133 3 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 true
private noncomputable def ibox142 : Fin 4 → FixedTape.I := splitI ibox141 2 19179738188473527080176482181428281523418786667798278978373162672499150890052611144076403880755200000000000000000000000 false
private noncomputable def ibox143 : Fin 4 → FixedTape.I := splitI ibox142 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox144 : Fin 4 → FixedTape.I := splitI ibox142 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox145 : Fin 4 → FixedTape.I := splitI ibox141 2 19179738188473527080176482181428281523418786667798278978373162672499150890052611144076403880755200000000000000000000000 true
private noncomputable def ibox146 : Fin 4 → FixedTape.I := splitI ibox145 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox147 : Fin 4 → FixedTape.I := splitI ibox145 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox148 : Fin 4 → FixedTape.I := splitI ibox132 2 21310820209415030089084980201586979470465318519775865531525736302776834322280679048973782089728000000000000000000000000 true
private noncomputable def ibox149 : Fin 4 → FixedTape.I := splitI ibox148 3 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 false
private noncomputable def ibox150 : Fin 4 → FixedTape.I := splitI ibox149 2 23441902230356533097993478221745677417511850371753452084678309933054517754508746953871160298700800000000000000000000000 false
private noncomputable def ibox151 : Fin 4 → FixedTape.I := splitI ibox150 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox152 : Fin 4 → FixedTape.I := splitI ibox150 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox153 : Fin 4 → FixedTape.I := splitI ibox149 2 23441902230356533097993478221745677417511850371753452084678309933054517754508746953871160298700800000000000000000000000 true
private noncomputable def ibox154 : Fin 4 → FixedTape.I := splitI ibox153 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox155 : Fin 4 → FixedTape.I := splitI ibox153 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox156 : Fin 4 → FixedTape.I := splitI ibox148 3 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 true
private noncomputable def ibox157 : Fin 4 → FixedTape.I := splitI ibox156 2 23441902230356533097993478221745677417511850371753452084678309933054517754508746953871160298700800000000000000000000000 false
private noncomputable def ibox158 : Fin 4 → FixedTape.I := splitI ibox157 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox159 : Fin 4 → FixedTape.I := splitI ibox157 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox160 : Fin 4 → FixedTape.I := splitI ibox156 2 23441902230356533097993478221745677417511850371753452084678309933054517754508746953871160298700800000000000000000000000 true
private noncomputable def ibox161 : Fin 4 → FixedTape.I := splitI ibox160 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox162 : Fin 4 → FixedTape.I := splitI ibox160 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox163 : Fin 4 → FixedTape.I := splitI ibox91 2 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 true
private noncomputable def ibox164 : Fin 4 → FixedTape.I := splitI ibox163 3 17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 false
private noncomputable def ibox165 : Fin 4 → FixedTape.I := splitI ibox164 3 8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 false
private noncomputable def ibox166 : Fin 4 → FixedTape.I := splitI ibox165 2 29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 false
private noncomputable def ibox167 : Fin 4 → FixedTape.I := splitI ibox166 3 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 false
private noncomputable def ibox168 : Fin 4 → FixedTape.I := splitI ibox167 2 27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 false
private noncomputable def ibox169 : Fin 4 → FixedTape.I := splitI ibox168 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox170 : Fin 4 → FixedTape.I := splitI ibox168 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox171 : Fin 4 → FixedTape.I := splitI ibox167 2 27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 true
private noncomputable def ibox172 : Fin 4 → FixedTape.I := splitI ibox171 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox173 : Fin 4 → FixedTape.I := splitI ibox171 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox174 : Fin 4 → FixedTape.I := splitI ibox166 3 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 true
private noncomputable def ibox175 : Fin 4 → FixedTape.I := splitI ibox174 2 27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 false
private noncomputable def ibox176 : Fin 4 → FixedTape.I := splitI ibox175 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox177 : Fin 4 → FixedTape.I := splitI ibox175 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox178 : Fin 4 → FixedTape.I := splitI ibox174 2 27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 true
private noncomputable def ibox179 : Fin 4 → FixedTape.I := splitI ibox178 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox180 : Fin 4 → FixedTape.I := splitI ibox178 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox181 : Fin 4 → FixedTape.I := splitI ibox165 2 29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 true
private noncomputable def ibox182 : Fin 4 → FixedTape.I := splitI ibox181 3 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 false
private noncomputable def ibox183 : Fin 4 → FixedTape.I := splitI ibox182 2 31966230314122545133627470302380469205697977779663798297288604454165251483421018573460673134592000000000000000000000000 false
private noncomputable def ibox184 : Fin 4 → FixedTape.I := splitI ibox183 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox185 : Fin 4 → FixedTape.I := splitI ibox183 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox186 : Fin 4 → FixedTape.I := splitI ibox182 2 31966230314122545133627470302380469205697977779663798297288604454165251483421018573460673134592000000000000000000000000 true
private noncomputable def ibox187 : Fin 4 → FixedTape.I := splitI ibox186 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox188 : Fin 4 → FixedTape.I := splitI ibox186 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox189 : Fin 4 → FixedTape.I := splitI ibox181 3 4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 true
private noncomputable def ibox190 : Fin 4 → FixedTape.I := splitI ibox189 2 31966230314122545133627470302380469205697977779663798297288604454165251483421018573460673134592000000000000000000000000 false
private noncomputable def ibox191 : Fin 4 → FixedTape.I := splitI ibox190 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox192 : Fin 4 → FixedTape.I := splitI ibox190 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox193 : Fin 4 → FixedTape.I := splitI ibox189 2 31966230314122545133627470302380469205697977779663798297288604454165251483421018573460673134592000000000000000000000000 true
private noncomputable def ibox194 : Fin 4 → FixedTape.I := splitI ibox193 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox195 : Fin 4 → FixedTape.I := splitI ibox193 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox196 : Fin 4 → FixedTape.I := splitI ibox164 3 8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 true
private noncomputable def ibox197 : Fin 4 → FixedTape.I := splitI ibox196 2 29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 false
private noncomputable def ibox198 : Fin 4 → FixedTape.I := splitI ibox197 2 27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 false
private noncomputable def ibox199 : Fin 4 → FixedTape.I := splitI ibox198 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox200 : Fin 4 → FixedTape.I := splitI ibox198 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox201 : Fin 4 → FixedTape.I := splitI ibox197 2 27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 true
private noncomputable def ibox202 : Fin 4 → FixedTape.I := splitI ibox201 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox203 : Fin 4 → FixedTape.I := splitI ibox201 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox204 : Fin 4 → FixedTape.I := splitI ibox196 2 29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 true
private noncomputable def ibox205 : Fin 4 → FixedTape.I := splitI ibox204 3 12786492125649018053450988120952187682279191111865519318915441781666100593368407429384269253836800000000000000000000000 false
private noncomputable def ibox206 : Fin 4 → FixedTape.I := splitI ibox205 2 31966230314122545133627470302380469205697977779663798297288604454165251483421018573460673134592000000000000000000000000 false
private noncomputable def ibox207 : Fin 4 → FixedTape.I := splitI ibox206 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox208 : Fin 4 → FixedTape.I := splitI ibox206 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox209 : Fin 4 → FixedTape.I := splitI ibox205 2 31966230314122545133627470302380469205697977779663798297288604454165251483421018573460673134592000000000000000000000000 true
private noncomputable def ibox210 : Fin 4 → FixedTape.I := splitI ibox209 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox211 : Fin 4 → FixedTape.I := splitI ibox209 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox212 : Fin 4 → FixedTape.I := splitI ibox204 3 12786492125649018053450988120952187682279191111865519318915441781666100593368407429384269253836800000000000000000000000 true
private noncomputable def ibox213 : Fin 4 → FixedTape.I := splitI ibox212 2 31966230314122545133627470302380469205697977779663798297288604454165251483421018573460673134592000000000000000000000000 false
private noncomputable def ibox214 : Fin 4 → FixedTape.I := splitI ibox213 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox215 : Fin 4 → FixedTape.I := splitI ibox213 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox216 : Fin 4 → FixedTape.I := splitI ibox212 2 31966230314122545133627470302380469205697977779663798297288604454165251483421018573460673134592000000000000000000000000 true
private noncomputable def ibox217 : Fin 4 → FixedTape.I := splitI ibox216 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox218 : Fin 4 → FixedTape.I := splitI ibox216 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox219 : Fin 4 → FixedTape.I := splitI ibox163 3 17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 true
private noncomputable def ibox220 : Fin 4 → FixedTape.I := splitI ibox219 2 29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 false
private noncomputable def ibox221 : Fin 4 → FixedTape.I := splitI ibox220 3 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 false
private noncomputable def ibox222 : Fin 4 → FixedTape.I := splitI ibox221 2 27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 false
private noncomputable def ibox223 : Fin 4 → FixedTape.I := splitI ibox222 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox224 : Fin 4 → FixedTape.I := splitI ibox222 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox225 : Fin 4 → FixedTape.I := splitI ibox221 2 27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 true
private noncomputable def ibox226 : Fin 4 → FixedTape.I := splitI ibox225 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox227 : Fin 4 → FixedTape.I := splitI ibox225 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox228 : Fin 4 → FixedTape.I := splitI ibox220 3 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 true
private noncomputable def ibox229 : Fin 4 → FixedTape.I := splitI ibox228 2 27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 false
private noncomputable def ibox230 : Fin 4 → FixedTape.I := splitI ibox229 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox231 : Fin 4 → FixedTape.I := splitI ibox229 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox232 : Fin 4 → FixedTape.I := splitI ibox228 2 27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 true
private noncomputable def ibox233 : Fin 4 → FixedTape.I := splitI ibox232 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox234 : Fin 4 → FixedTape.I := splitI ibox232 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox235 : Fin 4 → FixedTape.I := splitI ibox219 2 29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 true
private noncomputable def ibox236 : Fin 4 → FixedTape.I := splitI ibox235 3 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 false
private noncomputable def ibox237 : Fin 4 → FixedTape.I := splitI ibox236 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox238 : Fin 4 → FixedTape.I := splitI ibox237 3 21310820209415030089084980201586979470465318519775865531525736302776834322280679048973782089728000000000000000000000000 false
private noncomputable def ibox239 : Fin 4 → FixedTape.I := splitI ibox237 3 21310820209415030089084980201586979470465318519775865531525736302776834322280679048973782089728000000000000000000000000 true
private noncomputable def ibox240 : Fin 4 → FixedTape.I := splitI ibox236 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox241 : Fin 4 → FixedTape.I := splitI ibox240 3 21310820209415030089084980201586979470465318519775865531525736302776834322280679048973782089728000000000000000000000000 false
private noncomputable def ibox242 : Fin 4 → FixedTape.I := splitI ibox240 3 21310820209415030089084980201586979470465318519775865531525736302776834322280679048973782089728000000000000000000000000 true
private noncomputable def ibox243 : Fin 4 → FixedTape.I := splitI ibox235 3 25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 true
private noncomputable def ibox244 : Fin 4 → FixedTape.I := splitI ibox243 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 false
private noncomputable def ibox245 : Fin 4 → FixedTape.I := splitI ibox244 3 29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 false
private noncomputable def ibox246 : Fin 4 → FixedTape.I := splitI ibox244 3 29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 true
private noncomputable def ibox247 : Fin 4 → FixedTape.I := splitI ibox243 0 18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 true
private noncomputable def ibox248 : Fin 4 → FixedTape.I := splitI ibox247 3 29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 false
private noncomputable def ibox249 : Fin 4 → FixedTape.I := splitI ibox247 3 29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 true
private noncomputable def tree249 : TapeTree := .centered (candidateRows ibox249) (candidateRows (FixedTape.midBox ibox249))
attribute [irreducible] tree249
private theorem sign_249 : 2*denominator*(computed denominator (FixedTape.midBox ibox249)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox249).gradient k).lo.natAbs ((computed denominator ibox249).gradient k).hi.natAbs : Int)*((ibox249 k).hi-(ibox249 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox249
    (computed denominator ibox249) (computed denominator (FixedTape.midBox ibox249))
    (by decide +kernel)
private theorem midpoint_even_249 : ∀ k, 2 ∣ (ibox249 k).lo+(ibox249 k).hi := by decide +kernel
private theorem accepted_249 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox249) tree249 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox249 midpoint_even_249
  simp only [tree249,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox249,candidate_valid h (FixedTape.midBox ibox249),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox249 106 (FixedTape.rowsAux denominator ibox249 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox249) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_249
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
private noncomputable def tree247 : TapeTree := .split 3 (((29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree248 tree249
attribute [irreducible] tree247
private theorem accepted_247 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox247) tree247 = true := by
  simp only [tree247,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox247 3 (29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 : Int) false,decode_split denominator ibox247 3 (29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_248 h,accepted_249 h⟩
private noncomputable def tree246 : TapeTree := .centered (candidateRows ibox246) (candidateRows (FixedTape.midBox ibox246))
attribute [irreducible] tree246
private theorem sign_246 : 2*denominator*(computed denominator (FixedTape.midBox ibox246)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox246).gradient k).lo.natAbs ((computed denominator ibox246).gradient k).hi.natAbs : Int)*((ibox246 k).hi-(ibox246 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox246
    (computed denominator ibox246) (computed denominator (FixedTape.midBox ibox246))
    (by decide +kernel)
private theorem midpoint_even_246 : ∀ k, 2 ∣ (ibox246 k).lo+(ibox246 k).hi := by decide +kernel
private theorem accepted_246 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox246) tree246 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox246 midpoint_even_246
  simp only [tree246,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox246,candidate_valid h (FixedTape.midBox ibox246),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox246 106 (FixedTape.rowsAux denominator ibox246 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox246) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_246
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
private noncomputable def tree244 : TapeTree := .split 3 (((29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree245 tree246
attribute [irreducible] tree244
private theorem accepted_244 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox244) tree244 = true := by
  simp only [tree244,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox244 3 (29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 : Int) false,decode_split denominator ibox244 3 (29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_245 h,accepted_246 h⟩
private noncomputable def tree243 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree244 tree247
attribute [irreducible] tree243
private theorem accepted_243 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox243) tree243 = true := by
  simp only [tree243,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox243 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox243 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_244 h,accepted_247 h⟩
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
private noncomputable def tree240 : TapeTree := .split 3 (((21310820209415030089084980201586979470465318519775865531525736302776834322280679048973782089728000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree241 tree242
attribute [irreducible] tree240
private theorem accepted_240 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox240) tree240 = true := by
  simp only [tree240,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox240 3 (21310820209415030089084980201586979470465318519775865531525736302776834322280679048973782089728000000000000000000000000 : Int) false,decode_split denominator ibox240 3 (21310820209415030089084980201586979470465318519775865531525736302776834322280679048973782089728000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_241 h,accepted_242 h⟩
private noncomputable def tree239 : TapeTree := .centered (candidateRows ibox239) (candidateRows (FixedTape.midBox ibox239))
attribute [irreducible] tree239
private theorem sign_239 : 2*denominator*(computed denominator (FixedTape.midBox ibox239)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox239).gradient k).lo.natAbs ((computed denominator ibox239).gradient k).hi.natAbs : Int)*((ibox239 k).hi-(ibox239 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox239
    (computed denominator ibox239) (computed denominator (FixedTape.midBox ibox239))
    (by decide +kernel)
private theorem midpoint_even_239 : ∀ k, 2 ∣ (ibox239 k).lo+(ibox239 k).hi := by decide +kernel
private theorem accepted_239 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox239) tree239 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox239 midpoint_even_239
  simp only [tree239,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox239,candidate_valid h (FixedTape.midBox ibox239),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox239 106 (FixedTape.rowsAux denominator ibox239 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox239) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_239
private noncomputable def tree238 : TapeTree := .centered (candidateRows ibox238) (candidateRows (FixedTape.midBox ibox238))
attribute [irreducible] tree238
private theorem sign_238 : 2*denominator*(computed denominator (FixedTape.midBox ibox238)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox238).gradient k).lo.natAbs ((computed denominator ibox238).gradient k).hi.natAbs : Int)*((ibox238 k).hi-(ibox238 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox238
    (computed denominator ibox238) (computed denominator (FixedTape.midBox ibox238))
    (by decide +kernel)
private theorem midpoint_even_238 : ∀ k, 2 ∣ (ibox238 k).lo+(ibox238 k).hi := by decide +kernel
private theorem accepted_238 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox238) tree238 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox238 midpoint_even_238
  simp only [tree238,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox238,candidate_valid h (FixedTape.midBox ibox238),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox238 106 (FixedTape.rowsAux denominator ibox238 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox238) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_238
private noncomputable def tree237 : TapeTree := .split 3 (((21310820209415030089084980201586979470465318519775865531525736302776834322280679048973782089728000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree238 tree239
attribute [irreducible] tree237
private theorem accepted_237 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox237) tree237 = true := by
  simp only [tree237,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox237 3 (21310820209415030089084980201586979470465318519775865531525736302776834322280679048973782089728000000000000000000000000 : Int) false,decode_split denominator ibox237 3 (21310820209415030089084980201586979470465318519775865531525736302776834322280679048973782089728000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_238 h,accepted_239 h⟩
private noncomputable def tree236 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree237 tree240
attribute [irreducible] tree236
private theorem accepted_236 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox236) tree236 = true := by
  simp only [tree236,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox236 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox236 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_237 h,accepted_240 h⟩
private noncomputable def tree235 : TapeTree := .split 3 (((25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree236 tree243
attribute [irreducible] tree235
private theorem accepted_235 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox235) tree235 = true := by
  simp only [tree235,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox235 3 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) false,decode_split denominator ibox235 3 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_236 h,accepted_243 h⟩
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
private noncomputable def tree233 : TapeTree := .centered (candidateRows ibox233) (candidateRows (FixedTape.midBox ibox233))
attribute [irreducible] tree233
private theorem sign_233 : 2*denominator*(computed denominator (FixedTape.midBox ibox233)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox233).gradient k).lo.natAbs ((computed denominator ibox233).gradient k).hi.natAbs : Int)*((ibox233 k).hi-(ibox233 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox233
    (computed denominator ibox233) (computed denominator (FixedTape.midBox ibox233))
    (by decide +kernel)
private theorem midpoint_even_233 : ∀ k, 2 ∣ (ibox233 k).lo+(ibox233 k).hi := by decide +kernel
private theorem accepted_233 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox233) tree233 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox233 midpoint_even_233
  simp only [tree233,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox233,candidate_valid h (FixedTape.midBox ibox233),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox233 106 (FixedTape.rowsAux denominator ibox233 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox233) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_233
private noncomputable def tree232 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree233 tree234
attribute [irreducible] tree232
private theorem accepted_232 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox232) tree232 = true := by
  simp only [tree232,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox232 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox232 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_233 h,accepted_234 h⟩
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
private noncomputable def tree230 : TapeTree := .centered (candidateRows ibox230) (candidateRows (FixedTape.midBox ibox230))
attribute [irreducible] tree230
private theorem sign_230 : 2*denominator*(computed denominator (FixedTape.midBox ibox230)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox230).gradient k).lo.natAbs ((computed denominator ibox230).gradient k).hi.natAbs : Int)*((ibox230 k).hi-(ibox230 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox230
    (computed denominator ibox230) (computed denominator (FixedTape.midBox ibox230))
    (by decide +kernel)
private theorem midpoint_even_230 : ∀ k, 2 ∣ (ibox230 k).lo+(ibox230 k).hi := by decide +kernel
private theorem accepted_230 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox230) tree230 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox230 midpoint_even_230
  simp only [tree230,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox230,candidate_valid h (FixedTape.midBox ibox230),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox230 106 (FixedTape.rowsAux denominator ibox230 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox230) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_230
private noncomputable def tree229 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree230 tree231
attribute [irreducible] tree229
private theorem accepted_229 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox229) tree229 = true := by
  simp only [tree229,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox229 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox229 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_230 h,accepted_231 h⟩
private noncomputable def tree228 : TapeTree := .split 2 (((27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree229 tree232
attribute [irreducible] tree228
private theorem accepted_228 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox228) tree228 = true := by
  simp only [tree228,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox228 2 (27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 : Int) false,decode_split denominator ibox228 2 (27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_229 h,accepted_232 h⟩
private noncomputable def tree227 : TapeTree := .centered (candidateRows ibox227) (candidateRows (FixedTape.midBox ibox227))
attribute [irreducible] tree227
private theorem sign_227 : 2*denominator*(computed denominator (FixedTape.midBox ibox227)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox227).gradient k).lo.natAbs ((computed denominator ibox227).gradient k).hi.natAbs : Int)*((ibox227 k).hi-(ibox227 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox227
    (computed denominator ibox227) (computed denominator (FixedTape.midBox ibox227))
    (by decide +kernel)
private theorem midpoint_even_227 : ∀ k, 2 ∣ (ibox227 k).lo+(ibox227 k).hi := by decide +kernel
private theorem accepted_227 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox227) tree227 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox227 midpoint_even_227
  simp only [tree227,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox227,candidate_valid h (FixedTape.midBox ibox227),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox227 106 (FixedTape.rowsAux denominator ibox227 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox227) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_227
private noncomputable def tree226 : TapeTree := .centered (candidateRows ibox226) (candidateRows (FixedTape.midBox ibox226))
attribute [irreducible] tree226
private theorem sign_226 : 2*denominator*(computed denominator (FixedTape.midBox ibox226)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox226).gradient k).lo.natAbs ((computed denominator ibox226).gradient k).hi.natAbs : Int)*((ibox226 k).hi-(ibox226 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox226
    (computed denominator ibox226) (computed denominator (FixedTape.midBox ibox226))
    (by decide +kernel)
private theorem midpoint_even_226 : ∀ k, 2 ∣ (ibox226 k).lo+(ibox226 k).hi := by decide +kernel
private theorem accepted_226 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox226) tree226 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox226 midpoint_even_226
  simp only [tree226,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox226,candidate_valid h (FixedTape.midBox ibox226),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox226 106 (FixedTape.rowsAux denominator ibox226 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox226) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_226
private noncomputable def tree225 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree226 tree227
attribute [irreducible] tree225
private theorem accepted_225 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox225) tree225 = true := by
  simp only [tree225,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox225 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox225 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_226 h,accepted_227 h⟩
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
private noncomputable def tree222 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree223 tree224
attribute [irreducible] tree222
private theorem accepted_222 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox222) tree222 = true := by
  simp only [tree222,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox222 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox222 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_223 h,accepted_224 h⟩
private noncomputable def tree221 : TapeTree := .split 2 (((27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree222 tree225
attribute [irreducible] tree221
private theorem accepted_221 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox221) tree221 = true := by
  simp only [tree221,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox221 2 (27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 : Int) false,decode_split denominator ibox221 2 (27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_222 h,accepted_225 h⟩
private noncomputable def tree220 : TapeTree := .split 3 (((25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree221 tree228
attribute [irreducible] tree220
private theorem accepted_220 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox220) tree220 = true := by
  simp only [tree220,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox220 3 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) false,decode_split denominator ibox220 3 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_221 h,accepted_228 h⟩
private noncomputable def tree219 : TapeTree := .split 2 (((29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree220 tree235
attribute [irreducible] tree219
private theorem accepted_219 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox219) tree219 = true := by
  simp only [tree219,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox219 2 (29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 : Int) false,decode_split denominator ibox219 2 (29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_220 h,accepted_235 h⟩
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
private noncomputable def tree216 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree217 tree218
attribute [irreducible] tree216
private theorem accepted_216 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox216) tree216 = true := by
  simp only [tree216,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox216 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox216 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_217 h,accepted_218 h⟩
private noncomputable def tree215 : TapeTree := .centered (candidateRows ibox215) (candidateRows (FixedTape.midBox ibox215))
attribute [irreducible] tree215
private theorem sign_215 : 2*denominator*(computed denominator (FixedTape.midBox ibox215)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox215).gradient k).lo.natAbs ((computed denominator ibox215).gradient k).hi.natAbs : Int)*((ibox215 k).hi-(ibox215 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox215
    (computed denominator ibox215) (computed denominator (FixedTape.midBox ibox215))
    (by decide +kernel)
private theorem midpoint_even_215 : ∀ k, 2 ∣ (ibox215 k).lo+(ibox215 k).hi := by decide +kernel
private theorem accepted_215 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox215) tree215 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox215 midpoint_even_215
  simp only [tree215,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox215,candidate_valid h (FixedTape.midBox ibox215),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox215 106 (FixedTape.rowsAux denominator ibox215 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox215) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_215
private noncomputable def tree214 : TapeTree := .centered (candidateRows ibox214) (candidateRows (FixedTape.midBox ibox214))
attribute [irreducible] tree214
private theorem sign_214 : 2*denominator*(computed denominator (FixedTape.midBox ibox214)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox214).gradient k).lo.natAbs ((computed denominator ibox214).gradient k).hi.natAbs : Int)*((ibox214 k).hi-(ibox214 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox214
    (computed denominator ibox214) (computed denominator (FixedTape.midBox ibox214))
    (by decide +kernel)
private theorem midpoint_even_214 : ∀ k, 2 ∣ (ibox214 k).lo+(ibox214 k).hi := by decide +kernel
private theorem accepted_214 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox214) tree214 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox214 midpoint_even_214
  simp only [tree214,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox214,candidate_valid h (FixedTape.midBox ibox214),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox214 106 (FixedTape.rowsAux denominator ibox214 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox214) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_214
private noncomputable def tree213 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree214 tree215
attribute [irreducible] tree213
private theorem accepted_213 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox213) tree213 = true := by
  simp only [tree213,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox213 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox213 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_214 h,accepted_215 h⟩
private noncomputable def tree212 : TapeTree := .split 2 (((31966230314122545133627470302380469205697977779663798297288604454165251483421018573460673134592000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree213 tree216
attribute [irreducible] tree212
private theorem accepted_212 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox212) tree212 = true := by
  simp only [tree212,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox212 2 (31966230314122545133627470302380469205697977779663798297288604454165251483421018573460673134592000000000000000000000000 : Int) false,decode_split denominator ibox212 2 (31966230314122545133627470302380469205697977779663798297288604454165251483421018573460673134592000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_213 h,accepted_216 h⟩
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
private noncomputable def tree210 : TapeTree := .centered (candidateRows ibox210) (candidateRows (FixedTape.midBox ibox210))
attribute [irreducible] tree210
private theorem sign_210 : 2*denominator*(computed denominator (FixedTape.midBox ibox210)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox210).gradient k).lo.natAbs ((computed denominator ibox210).gradient k).hi.natAbs : Int)*((ibox210 k).hi-(ibox210 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox210
    (computed denominator ibox210) (computed denominator (FixedTape.midBox ibox210))
    (by decide +kernel)
private theorem midpoint_even_210 : ∀ k, 2 ∣ (ibox210 k).lo+(ibox210 k).hi := by decide +kernel
private theorem accepted_210 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox210) tree210 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox210 midpoint_even_210
  simp only [tree210,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox210,candidate_valid h (FixedTape.midBox ibox210),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox210 106 (FixedTape.rowsAux denominator ibox210 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox210) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_210
private noncomputable def tree209 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree210 tree211
attribute [irreducible] tree209
private theorem accepted_209 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox209) tree209 = true := by
  simp only [tree209,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox209 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox209 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_210 h,accepted_211 h⟩
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
private noncomputable def tree207 : TapeTree := .centered (candidateRows ibox207) (candidateRows (FixedTape.midBox ibox207))
attribute [irreducible] tree207
private theorem sign_207 : 2*denominator*(computed denominator (FixedTape.midBox ibox207)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox207).gradient k).lo.natAbs ((computed denominator ibox207).gradient k).hi.natAbs : Int)*((ibox207 k).hi-(ibox207 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox207
    (computed denominator ibox207) (computed denominator (FixedTape.midBox ibox207))
    (by decide +kernel)
private theorem midpoint_even_207 : ∀ k, 2 ∣ (ibox207 k).lo+(ibox207 k).hi := by decide +kernel
private theorem accepted_207 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox207) tree207 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox207 midpoint_even_207
  simp only [tree207,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox207,candidate_valid h (FixedTape.midBox ibox207),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox207 106 (FixedTape.rowsAux denominator ibox207 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox207) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_207
private noncomputable def tree206 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree207 tree208
attribute [irreducible] tree206
private theorem accepted_206 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox206) tree206 = true := by
  simp only [tree206,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox206 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox206 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_207 h,accepted_208 h⟩
private noncomputable def tree205 : TapeTree := .split 2 (((31966230314122545133627470302380469205697977779663798297288604454165251483421018573460673134592000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree206 tree209
attribute [irreducible] tree205
private theorem accepted_205 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox205) tree205 = true := by
  simp only [tree205,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox205 2 (31966230314122545133627470302380469205697977779663798297288604454165251483421018573460673134592000000000000000000000000 : Int) false,decode_split denominator ibox205 2 (31966230314122545133627470302380469205697977779663798297288604454165251483421018573460673134592000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_206 h,accepted_209 h⟩
private noncomputable def tree204 : TapeTree := .split 3 (((12786492125649018053450988120952187682279191111865519318915441781666100593368407429384269253836800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree205 tree212
attribute [irreducible] tree204
private theorem accepted_204 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox204) tree204 = true := by
  simp only [tree204,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox204 3 (12786492125649018053450988120952187682279191111865519318915441781666100593368407429384269253836800000000000000000000000 : Int) false,decode_split denominator ibox204 3 (12786492125649018053450988120952187682279191111865519318915441781666100593368407429384269253836800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_205 h,accepted_212 h⟩
private noncomputable def tree203 : TapeTree := .centered (candidateRows ibox203) (candidateRows (FixedTape.midBox ibox203))
attribute [irreducible] tree203
private theorem sign_203 : 2*denominator*(computed denominator (FixedTape.midBox ibox203)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox203).gradient k).lo.natAbs ((computed denominator ibox203).gradient k).hi.natAbs : Int)*((ibox203 k).hi-(ibox203 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox203
    (computed denominator ibox203) (computed denominator (FixedTape.midBox ibox203))
    (by decide +kernel)
private theorem midpoint_even_203 : ∀ k, 2 ∣ (ibox203 k).lo+(ibox203 k).hi := by decide +kernel
private theorem accepted_203 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox203) tree203 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox203 midpoint_even_203
  simp only [tree203,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox203,candidate_valid h (FixedTape.midBox ibox203),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox203 106 (FixedTape.rowsAux denominator ibox203 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox203) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_203
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
private noncomputable def tree201 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree202 tree203
attribute [irreducible] tree201
private theorem accepted_201 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox201) tree201 = true := by
  simp only [tree201,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox201 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox201 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_202 h,accepted_203 h⟩
private noncomputable def tree200 : TapeTree := .centered (candidateRows ibox200) (candidateRows (FixedTape.midBox ibox200))
attribute [irreducible] tree200
private theorem sign_200 : 2*denominator*(computed denominator (FixedTape.midBox ibox200)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox200).gradient k).lo.natAbs ((computed denominator ibox200).gradient k).hi.natAbs : Int)*((ibox200 k).hi-(ibox200 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox200
    (computed denominator ibox200) (computed denominator (FixedTape.midBox ibox200))
    (by decide +kernel)
private theorem midpoint_even_200 : ∀ k, 2 ∣ (ibox200 k).lo+(ibox200 k).hi := by decide +kernel
private theorem accepted_200 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox200) tree200 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox200 midpoint_even_200
  simp only [tree200,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox200,candidate_valid h (FixedTape.midBox ibox200),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox200 106 (FixedTape.rowsAux denominator ibox200 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox200) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_200
private noncomputable def tree199 : TapeTree := .centered (candidateRows ibox199) (candidateRows (FixedTape.midBox ibox199))
attribute [irreducible] tree199
private theorem sign_199 : 2*denominator*(computed denominator (FixedTape.midBox ibox199)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox199).gradient k).lo.natAbs ((computed denominator ibox199).gradient k).hi.natAbs : Int)*((ibox199 k).hi-(ibox199 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox199
    (computed denominator ibox199) (computed denominator (FixedTape.midBox ibox199))
    (by decide +kernel)
private theorem midpoint_even_199 : ∀ k, 2 ∣ (ibox199 k).lo+(ibox199 k).hi := by decide +kernel
private theorem accepted_199 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox199) tree199 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox199 midpoint_even_199
  simp only [tree199,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox199,candidate_valid h (FixedTape.midBox ibox199),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox199 106 (FixedTape.rowsAux denominator ibox199 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox199) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_199
private noncomputable def tree198 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree199 tree200
attribute [irreducible] tree198
private theorem accepted_198 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox198) tree198 = true := by
  simp only [tree198,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox198 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox198 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_199 h,accepted_200 h⟩
private noncomputable def tree197 : TapeTree := .split 2 (((27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree198 tree201
attribute [irreducible] tree197
private theorem accepted_197 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox197) tree197 = true := by
  simp only [tree197,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox197 2 (27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 : Int) false,decode_split denominator ibox197 2 (27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_198 h,accepted_201 h⟩
private noncomputable def tree196 : TapeTree := .split 2 (((29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree197 tree204
attribute [irreducible] tree196
private theorem accepted_196 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox196) tree196 = true := by
  simp only [tree196,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox196 2 (29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 : Int) false,decode_split denominator ibox196 2 (29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_197 h,accepted_204 h⟩
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
private noncomputable def tree193 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree194 tree195
attribute [irreducible] tree193
private theorem accepted_193 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox193) tree193 = true := by
  simp only [tree193,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox193 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox193 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_194 h,accepted_195 h⟩
private noncomputable def tree192 : TapeTree := .centered (candidateRows ibox192) (candidateRows (FixedTape.midBox ibox192))
attribute [irreducible] tree192
private theorem sign_192 : 2*denominator*(computed denominator (FixedTape.midBox ibox192)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox192).gradient k).lo.natAbs ((computed denominator ibox192).gradient k).hi.natAbs : Int)*((ibox192 k).hi-(ibox192 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox192
    (computed denominator ibox192) (computed denominator (FixedTape.midBox ibox192))
    (by decide +kernel)
private theorem midpoint_even_192 : ∀ k, 2 ∣ (ibox192 k).lo+(ibox192 k).hi := by decide +kernel
private theorem accepted_192 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox192) tree192 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox192 midpoint_even_192
  simp only [tree192,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox192,candidate_valid h (FixedTape.midBox ibox192),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox192 106 (FixedTape.rowsAux denominator ibox192 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox192) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_192
private noncomputable def tree191 : TapeTree := .centered (candidateRows ibox191) (candidateRows (FixedTape.midBox ibox191))
attribute [irreducible] tree191
private theorem sign_191 : 2*denominator*(computed denominator (FixedTape.midBox ibox191)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox191).gradient k).lo.natAbs ((computed denominator ibox191).gradient k).hi.natAbs : Int)*((ibox191 k).hi-(ibox191 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox191
    (computed denominator ibox191) (computed denominator (FixedTape.midBox ibox191))
    (by decide +kernel)
private theorem midpoint_even_191 : ∀ k, 2 ∣ (ibox191 k).lo+(ibox191 k).hi := by decide +kernel
private theorem accepted_191 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox191) tree191 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox191 midpoint_even_191
  simp only [tree191,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox191,candidate_valid h (FixedTape.midBox ibox191),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox191 106 (FixedTape.rowsAux denominator ibox191 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox191) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_191
private noncomputable def tree190 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree191 tree192
attribute [irreducible] tree190
private theorem accepted_190 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox190) tree190 = true := by
  simp only [tree190,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox190 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox190 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_191 h,accepted_192 h⟩
private noncomputable def tree189 : TapeTree := .split 2 (((31966230314122545133627470302380469205697977779663798297288604454165251483421018573460673134592000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree190 tree193
attribute [irreducible] tree189
private theorem accepted_189 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox189) tree189 = true := by
  simp only [tree189,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox189 2 (31966230314122545133627470302380469205697977779663798297288604454165251483421018573460673134592000000000000000000000000 : Int) false,decode_split denominator ibox189 2 (31966230314122545133627470302380469205697977779663798297288604454165251483421018573460673134592000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_190 h,accepted_193 h⟩
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
private noncomputable def tree187 : TapeTree := .centered (candidateRows ibox187) (candidateRows (FixedTape.midBox ibox187))
attribute [irreducible] tree187
private theorem sign_187 : 2*denominator*(computed denominator (FixedTape.midBox ibox187)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox187).gradient k).lo.natAbs ((computed denominator ibox187).gradient k).hi.natAbs : Int)*((ibox187 k).hi-(ibox187 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox187
    (computed denominator ibox187) (computed denominator (FixedTape.midBox ibox187))
    (by decide +kernel)
private theorem midpoint_even_187 : ∀ k, 2 ∣ (ibox187 k).lo+(ibox187 k).hi := by decide +kernel
private theorem accepted_187 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox187) tree187 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox187 midpoint_even_187
  simp only [tree187,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox187,candidate_valid h (FixedTape.midBox ibox187),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox187 106 (FixedTape.rowsAux denominator ibox187 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox187) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_187
private noncomputable def tree186 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree187 tree188
attribute [irreducible] tree186
private theorem accepted_186 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox186) tree186 = true := by
  simp only [tree186,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox186 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox186 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_187 h,accepted_188 h⟩
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
private noncomputable def tree184 : TapeTree := .centered (candidateRows ibox184) (candidateRows (FixedTape.midBox ibox184))
attribute [irreducible] tree184
private theorem sign_184 : 2*denominator*(computed denominator (FixedTape.midBox ibox184)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox184).gradient k).lo.natAbs ((computed denominator ibox184).gradient k).hi.natAbs : Int)*((ibox184 k).hi-(ibox184 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox184
    (computed denominator ibox184) (computed denominator (FixedTape.midBox ibox184))
    (by decide +kernel)
private theorem midpoint_even_184 : ∀ k, 2 ∣ (ibox184 k).lo+(ibox184 k).hi := by decide +kernel
private theorem accepted_184 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox184) tree184 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox184 midpoint_even_184
  simp only [tree184,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox184,candidate_valid h (FixedTape.midBox ibox184),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox184 106 (FixedTape.rowsAux denominator ibox184 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox184) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_184
private noncomputable def tree183 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree184 tree185
attribute [irreducible] tree183
private theorem accepted_183 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox183) tree183 = true := by
  simp only [tree183,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox183 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox183 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_184 h,accepted_185 h⟩
private noncomputable def tree182 : TapeTree := .split 2 (((31966230314122545133627470302380469205697977779663798297288604454165251483421018573460673134592000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree183 tree186
attribute [irreducible] tree182
private theorem accepted_182 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox182) tree182 = true := by
  simp only [tree182,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox182 2 (31966230314122545133627470302380469205697977779663798297288604454165251483421018573460673134592000000000000000000000000 : Int) false,decode_split denominator ibox182 2 (31966230314122545133627470302380469205697977779663798297288604454165251483421018573460673134592000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_183 h,accepted_186 h⟩
private noncomputable def tree181 : TapeTree := .split 3 (((4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree182 tree189
attribute [irreducible] tree181
private theorem accepted_181 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox181) tree181 = true := by
  simp only [tree181,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox181 3 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) false,decode_split denominator ibox181 3 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_182 h,accepted_189 h⟩
private noncomputable def tree180 : TapeTree := .centered (candidateRows ibox180) (candidateRows (FixedTape.midBox ibox180))
attribute [irreducible] tree180
private theorem sign_180 : 2*denominator*(computed denominator (FixedTape.midBox ibox180)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox180).gradient k).lo.natAbs ((computed denominator ibox180).gradient k).hi.natAbs : Int)*((ibox180 k).hi-(ibox180 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox180
    (computed denominator ibox180) (computed denominator (FixedTape.midBox ibox180))
    (by decide +kernel)
private theorem midpoint_even_180 : ∀ k, 2 ∣ (ibox180 k).lo+(ibox180 k).hi := by decide +kernel
private theorem accepted_180 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox180) tree180 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox180 midpoint_even_180
  simp only [tree180,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox180,candidate_valid h (FixedTape.midBox ibox180),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox180 106 (FixedTape.rowsAux denominator ibox180 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox180) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_180
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
private noncomputable def tree178 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree179 tree180
attribute [irreducible] tree178
private theorem accepted_178 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox178) tree178 = true := by
  simp only [tree178,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox178 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox178 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_179 h,accepted_180 h⟩
private noncomputable def tree177 : TapeTree := .centered (candidateRows ibox177) (candidateRows (FixedTape.midBox ibox177))
attribute [irreducible] tree177
private theorem sign_177 : 2*denominator*(computed denominator (FixedTape.midBox ibox177)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox177).gradient k).lo.natAbs ((computed denominator ibox177).gradient k).hi.natAbs : Int)*((ibox177 k).hi-(ibox177 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox177
    (computed denominator ibox177) (computed denominator (FixedTape.midBox ibox177))
    (by decide +kernel)
private theorem midpoint_even_177 : ∀ k, 2 ∣ (ibox177 k).lo+(ibox177 k).hi := by decide +kernel
private theorem accepted_177 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox177) tree177 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox177 midpoint_even_177
  simp only [tree177,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox177,candidate_valid h (FixedTape.midBox ibox177),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox177 106 (FixedTape.rowsAux denominator ibox177 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox177) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_177
private noncomputable def tree176 : TapeTree := .centered (candidateRows ibox176) (candidateRows (FixedTape.midBox ibox176))
attribute [irreducible] tree176
private theorem sign_176 : 2*denominator*(computed denominator (FixedTape.midBox ibox176)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox176).gradient k).lo.natAbs ((computed denominator ibox176).gradient k).hi.natAbs : Int)*((ibox176 k).hi-(ibox176 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox176
    (computed denominator ibox176) (computed denominator (FixedTape.midBox ibox176))
    (by decide +kernel)
private theorem midpoint_even_176 : ∀ k, 2 ∣ (ibox176 k).lo+(ibox176 k).hi := by decide +kernel
private theorem accepted_176 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox176) tree176 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox176 midpoint_even_176
  simp only [tree176,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox176,candidate_valid h (FixedTape.midBox ibox176),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox176 106 (FixedTape.rowsAux denominator ibox176 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox176) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_176
private noncomputable def tree175 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree176 tree177
attribute [irreducible] tree175
private theorem accepted_175 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox175) tree175 = true := by
  simp only [tree175,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox175 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox175 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_176 h,accepted_177 h⟩
private noncomputable def tree174 : TapeTree := .split 2 (((27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree175 tree178
attribute [irreducible] tree174
private theorem accepted_174 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox174) tree174 = true := by
  simp only [tree174,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox174 2 (27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 : Int) false,decode_split denominator ibox174 2 (27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_175 h,accepted_178 h⟩
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
private noncomputable def tree172 : TapeTree := .centered (candidateRows ibox172) (candidateRows (FixedTape.midBox ibox172))
attribute [irreducible] tree172
private theorem sign_172 : 2*denominator*(computed denominator (FixedTape.midBox ibox172)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox172).gradient k).lo.natAbs ((computed denominator ibox172).gradient k).hi.natAbs : Int)*((ibox172 k).hi-(ibox172 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox172
    (computed denominator ibox172) (computed denominator (FixedTape.midBox ibox172))
    (by decide +kernel)
private theorem midpoint_even_172 : ∀ k, 2 ∣ (ibox172 k).lo+(ibox172 k).hi := by decide +kernel
private theorem accepted_172 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox172) tree172 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox172 midpoint_even_172
  simp only [tree172,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox172,candidate_valid h (FixedTape.midBox ibox172),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox172 106 (FixedTape.rowsAux denominator ibox172 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox172) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_172
private noncomputable def tree171 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree172 tree173
attribute [irreducible] tree171
private theorem accepted_171 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox171) tree171 = true := by
  simp only [tree171,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox171 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox171 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_172 h,accepted_173 h⟩
private noncomputable def tree170 : TapeTree := .centered (candidateRows ibox170) (candidateRows (FixedTape.midBox ibox170))
attribute [irreducible] tree170
private theorem sign_170 : 2*denominator*(computed denominator (FixedTape.midBox ibox170)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox170).gradient k).lo.natAbs ((computed denominator ibox170).gradient k).hi.natAbs : Int)*((ibox170 k).hi-(ibox170 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox170
    (computed denominator ibox170) (computed denominator (FixedTape.midBox ibox170))
    (by decide +kernel)
private theorem midpoint_even_170 : ∀ k, 2 ∣ (ibox170 k).lo+(ibox170 k).hi := by decide +kernel
private theorem accepted_170 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox170) tree170 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox170 midpoint_even_170
  simp only [tree170,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox170,candidate_valid h (FixedTape.midBox ibox170),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox170 106 (FixedTape.rowsAux denominator ibox170 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox170) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_170
private noncomputable def tree169 : TapeTree := .centered (candidateRows ibox169) (candidateRows (FixedTape.midBox ibox169))
attribute [irreducible] tree169
private theorem sign_169 : 2*denominator*(computed denominator (FixedTape.midBox ibox169)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox169).gradient k).lo.natAbs ((computed denominator ibox169).gradient k).hi.natAbs : Int)*((ibox169 k).hi-(ibox169 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox169
    (computed denominator ibox169) (computed denominator (FixedTape.midBox ibox169))
    (by decide +kernel)
private theorem midpoint_even_169 : ∀ k, 2 ∣ (ibox169 k).lo+(ibox169 k).hi := by decide +kernel
private theorem accepted_169 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox169) tree169 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox169 midpoint_even_169
  simp only [tree169,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox169,candidate_valid h (FixedTape.midBox ibox169),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox169 106 (FixedTape.rowsAux denominator ibox169 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox169) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_169
private noncomputable def tree168 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree169 tree170
attribute [irreducible] tree168
private theorem accepted_168 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox168) tree168 = true := by
  simp only [tree168,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox168 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox168 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_169 h,accepted_170 h⟩
private noncomputable def tree167 : TapeTree := .split 2 (((27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree168 tree171
attribute [irreducible] tree167
private theorem accepted_167 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox167) tree167 = true := by
  simp only [tree167,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox167 2 (27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 : Int) false,decode_split denominator ibox167 2 (27704066272239539115810474262063073311604914075708625190983457193609884618964882763665916716646400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_168 h,accepted_171 h⟩
private noncomputable def tree166 : TapeTree := .split 3 (((4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree167 tree174
attribute [irreducible] tree166
private theorem accepted_166 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox166) tree166 = true := by
  simp only [tree166,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox166 3 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) false,decode_split denominator ibox166 3 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_167 h,accepted_174 h⟩
private noncomputable def tree165 : TapeTree := .split 2 (((29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree166 tree181
attribute [irreducible] tree165
private theorem accepted_165 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox165) tree165 = true := by
  simp only [tree165,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox165 2 (29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 : Int) false,decode_split denominator ibox165 2 (29835148293181042124718972282221771258651445927686211744136030823887568051192950668563294925619200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_166 h,accepted_181 h⟩
private noncomputable def tree164 : TapeTree := .split 3 (((8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree165 tree196
attribute [irreducible] tree164
private theorem accepted_164 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox164) tree164 = true := by
  simp only [tree164,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox164 3 (8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) false,decode_split denominator ibox164 3 (8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_165 h,accepted_196 h⟩
private noncomputable def tree163 : TapeTree := .split 3 (((17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree164 tree219
attribute [irreducible] tree163
private theorem accepted_163 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox163) tree163 = true := by
  simp only [tree163,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox163 3 (17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) false,decode_split denominator ibox163 3 (17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_164 h,accepted_219 h⟩
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
private noncomputable def tree161 : TapeTree := .centered (candidateRows ibox161) (candidateRows (FixedTape.midBox ibox161))
attribute [irreducible] tree161
private theorem sign_161 : 2*denominator*(computed denominator (FixedTape.midBox ibox161)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox161).gradient k).lo.natAbs ((computed denominator ibox161).gradient k).hi.natAbs : Int)*((ibox161 k).hi-(ibox161 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox161
    (computed denominator ibox161) (computed denominator (FixedTape.midBox ibox161))
    (by decide +kernel)
private theorem midpoint_even_161 : ∀ k, 2 ∣ (ibox161 k).lo+(ibox161 k).hi := by decide +kernel
private theorem accepted_161 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox161) tree161 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox161 midpoint_even_161
  simp only [tree161,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox161,candidate_valid h (FixedTape.midBox ibox161),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox161 106 (FixedTape.rowsAux denominator ibox161 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox161) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_161
private noncomputable def tree160 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree161 tree162
attribute [irreducible] tree160
private theorem accepted_160 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox160) tree160 = true := by
  simp only [tree160,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox160 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox160 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_161 h,accepted_162 h⟩
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
private noncomputable def tree157 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree158 tree159
attribute [irreducible] tree157
private theorem accepted_157 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox157) tree157 = true := by
  simp only [tree157,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox157 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox157 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_158 h,accepted_159 h⟩
private noncomputable def tree156 : TapeTree := .split 2 (((23441902230356533097993478221745677417511850371753452084678309933054517754508746953871160298700800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree157 tree160
attribute [irreducible] tree156
private theorem accepted_156 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox156) tree156 = true := by
  simp only [tree156,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox156 2 (23441902230356533097993478221745677417511850371753452084678309933054517754508746953871160298700800000000000000000000000 : Int) false,decode_split denominator ibox156 2 (23441902230356533097993478221745677417511850371753452084678309933054517754508746953871160298700800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_157 h,accepted_160 h⟩
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
private noncomputable def tree154 : TapeTree := .centered (candidateRows ibox154) (candidateRows (FixedTape.midBox ibox154))
attribute [irreducible] tree154
private theorem sign_154 : 2*denominator*(computed denominator (FixedTape.midBox ibox154)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox154).gradient k).lo.natAbs ((computed denominator ibox154).gradient k).hi.natAbs : Int)*((ibox154 k).hi-(ibox154 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox154
    (computed denominator ibox154) (computed denominator (FixedTape.midBox ibox154))
    (by decide +kernel)
private theorem midpoint_even_154 : ∀ k, 2 ∣ (ibox154 k).lo+(ibox154 k).hi := by decide +kernel
private theorem accepted_154 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox154) tree154 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox154 midpoint_even_154
  simp only [tree154,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox154,candidate_valid h (FixedTape.midBox ibox154),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox154 106 (FixedTape.rowsAux denominator ibox154 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox154) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_154
private noncomputable def tree153 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree154 tree155
attribute [irreducible] tree153
private theorem accepted_153 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox153) tree153 = true := by
  simp only [tree153,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox153 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox153 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_154 h,accepted_155 h⟩
private noncomputable def tree152 : TapeTree := .centered (candidateRows ibox152) (candidateRows (FixedTape.midBox ibox152))
attribute [irreducible] tree152
private theorem sign_152 : 2*denominator*(computed denominator (FixedTape.midBox ibox152)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox152).gradient k).lo.natAbs ((computed denominator ibox152).gradient k).hi.natAbs : Int)*((ibox152 k).hi-(ibox152 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox152
    (computed denominator ibox152) (computed denominator (FixedTape.midBox ibox152))
    (by decide +kernel)
private theorem midpoint_even_152 : ∀ k, 2 ∣ (ibox152 k).lo+(ibox152 k).hi := by decide +kernel
private theorem accepted_152 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox152) tree152 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox152 midpoint_even_152
  simp only [tree152,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox152,candidate_valid h (FixedTape.midBox ibox152),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox152 106 (FixedTape.rowsAux denominator ibox152 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox152) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_152
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
private noncomputable def tree150 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree151 tree152
attribute [irreducible] tree150
private theorem accepted_150 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox150) tree150 = true := by
  simp only [tree150,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox150 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox150 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_151 h,accepted_152 h⟩
private noncomputable def tree149 : TapeTree := .split 2 (((23441902230356533097993478221745677417511850371753452084678309933054517754508746953871160298700800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree150 tree153
attribute [irreducible] tree149
private theorem accepted_149 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox149) tree149 = true := by
  simp only [tree149,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox149 2 (23441902230356533097993478221745677417511850371753452084678309933054517754508746953871160298700800000000000000000000000 : Int) false,decode_split denominator ibox149 2 (23441902230356533097993478221745677417511850371753452084678309933054517754508746953871160298700800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_150 h,accepted_153 h⟩
private noncomputable def tree148 : TapeTree := .split 3 (((25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree149 tree156
attribute [irreducible] tree148
private theorem accepted_148 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox148) tree148 = true := by
  simp only [tree148,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox148 3 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) false,decode_split denominator ibox148 3 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_149 h,accepted_156 h⟩
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
private noncomputable def tree146 : TapeTree := .centered (candidateRows ibox146) (candidateRows (FixedTape.midBox ibox146))
attribute [irreducible] tree146
private theorem sign_146 : 2*denominator*(computed denominator (FixedTape.midBox ibox146)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox146).gradient k).lo.natAbs ((computed denominator ibox146).gradient k).hi.natAbs : Int)*((ibox146 k).hi-(ibox146 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox146
    (computed denominator ibox146) (computed denominator (FixedTape.midBox ibox146))
    (by decide +kernel)
private theorem midpoint_even_146 : ∀ k, 2 ∣ (ibox146 k).lo+(ibox146 k).hi := by decide +kernel
private theorem accepted_146 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox146) tree146 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox146 midpoint_even_146
  simp only [tree146,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox146,candidate_valid h (FixedTape.midBox ibox146),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox146 106 (FixedTape.rowsAux denominator ibox146 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox146) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_146
private noncomputable def tree145 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree146 tree147
attribute [irreducible] tree145
private theorem accepted_145 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox145) tree145 = true := by
  simp only [tree145,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox145 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox145 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_146 h,accepted_147 h⟩
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
private noncomputable def tree142 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree143 tree144
attribute [irreducible] tree142
private theorem accepted_142 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox142) tree142 = true := by
  simp only [tree142,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox142 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox142 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_143 h,accepted_144 h⟩
private noncomputable def tree141 : TapeTree := .split 2 (((19179738188473527080176482181428281523418786667798278978373162672499150890052611144076403880755200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree142 tree145
attribute [irreducible] tree141
private theorem accepted_141 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox141) tree141 = true := by
  simp only [tree141,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox141 2 (19179738188473527080176482181428281523418786667798278978373162672499150890052611144076403880755200000000000000000000000 : Int) false,decode_split denominator ibox141 2 (19179738188473527080176482181428281523418786667798278978373162672499150890052611144076403880755200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_142 h,accepted_145 h⟩
private noncomputable def tree140 : TapeTree := .centered (candidateRows ibox140) (candidateRows (FixedTape.midBox ibox140))
attribute [irreducible] tree140
private theorem sign_140 : 2*denominator*(computed denominator (FixedTape.midBox ibox140)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox140).gradient k).lo.natAbs ((computed denominator ibox140).gradient k).hi.natAbs : Int)*((ibox140 k).hi-(ibox140 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox140
    (computed denominator ibox140) (computed denominator (FixedTape.midBox ibox140))
    (by decide +kernel)
private theorem midpoint_even_140 : ∀ k, 2 ∣ (ibox140 k).lo+(ibox140 k).hi := by decide +kernel
private theorem accepted_140 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox140) tree140 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox140 midpoint_even_140
  simp only [tree140,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox140,candidate_valid h (FixedTape.midBox ibox140),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox140 106 (FixedTape.rowsAux denominator ibox140 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox140) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_140
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
private noncomputable def tree138 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree139 tree140
attribute [irreducible] tree138
private theorem accepted_138 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox138) tree138 = true := by
  simp only [tree138,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox138 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox138 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_139 h,accepted_140 h⟩
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
private noncomputable def tree136 : TapeTree := .centered (candidateRows ibox136) (candidateRows (FixedTape.midBox ibox136))
attribute [irreducible] tree136
private theorem sign_136 : 2*denominator*(computed denominator (FixedTape.midBox ibox136)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox136).gradient k).lo.natAbs ((computed denominator ibox136).gradient k).hi.natAbs : Int)*((ibox136 k).hi-(ibox136 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox136
    (computed denominator ibox136) (computed denominator (FixedTape.midBox ibox136))
    (by decide +kernel)
private theorem midpoint_even_136 : ∀ k, 2 ∣ (ibox136 k).lo+(ibox136 k).hi := by decide +kernel
private theorem accepted_136 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox136) tree136 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox136 midpoint_even_136
  simp only [tree136,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox136,candidate_valid h (FixedTape.midBox ibox136),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox136 106 (FixedTape.rowsAux denominator ibox136 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox136) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_136
private noncomputable def tree135 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree136 tree137
attribute [irreducible] tree135
private theorem accepted_135 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox135) tree135 = true := by
  simp only [tree135,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox135 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox135 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_136 h,accepted_137 h⟩
private noncomputable def tree134 : TapeTree := .split 2 (((19179738188473527080176482181428281523418786667798278978373162672499150890052611144076403880755200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree135 tree138
attribute [irreducible] tree134
private theorem accepted_134 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox134) tree134 = true := by
  simp only [tree134,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox134 2 (19179738188473527080176482181428281523418786667798278978373162672499150890052611144076403880755200000000000000000000000 : Int) false,decode_split denominator ibox134 2 (19179738188473527080176482181428281523418786667798278978373162672499150890052611144076403880755200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_135 h,accepted_138 h⟩
private noncomputable def tree133 : TapeTree := .split 3 (((25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree134 tree141
attribute [irreducible] tree133
private theorem accepted_133 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox133) tree133 = true := by
  simp only [tree133,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox133 3 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) false,decode_split denominator ibox133 3 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_134 h,accepted_141 h⟩
private noncomputable def tree132 : TapeTree := .split 2 (((21310820209415030089084980201586979470465318519775865531525736302776834322280679048973782089728000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree133 tree148
attribute [irreducible] tree132
private theorem accepted_132 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox132) tree132 = true := by
  simp only [tree132,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox132 2 (21310820209415030089084980201586979470465318519775865531525736302776834322280679048973782089728000000000000000000000000 : Int) false,decode_split denominator ibox132 2 (21310820209415030089084980201586979470465318519775865531525736302776834322280679048973782089728000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_133 h,accepted_148 h⟩
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
private noncomputable def tree130 : TapeTree := .centered (candidateRows ibox130) (candidateRows (FixedTape.midBox ibox130))
attribute [irreducible] tree130
private theorem sign_130 : 2*denominator*(computed denominator (FixedTape.midBox ibox130)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox130).gradient k).lo.natAbs ((computed denominator ibox130).gradient k).hi.natAbs : Int)*((ibox130 k).hi-(ibox130 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox130
    (computed denominator ibox130) (computed denominator (FixedTape.midBox ibox130))
    (by decide +kernel)
private theorem midpoint_even_130 : ∀ k, 2 ∣ (ibox130 k).lo+(ibox130 k).hi := by decide +kernel
private theorem accepted_130 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox130) tree130 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox130 midpoint_even_130
  simp only [tree130,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox130,candidate_valid h (FixedTape.midBox ibox130),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox130 106 (FixedTape.rowsAux denominator ibox130 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox130) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_130
private noncomputable def tree129 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree130 tree131
attribute [irreducible] tree129
private theorem accepted_129 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox129) tree129 = true := by
  simp only [tree129,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox129 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox129 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_130 h,accepted_131 h⟩
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
private noncomputable def tree127 : TapeTree := .centered (candidateRows ibox127) (candidateRows (FixedTape.midBox ibox127))
attribute [irreducible] tree127
private theorem sign_127 : 2*denominator*(computed denominator (FixedTape.midBox ibox127)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox127).gradient k).lo.natAbs ((computed denominator ibox127).gradient k).hi.natAbs : Int)*((ibox127 k).hi-(ibox127 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox127
    (computed denominator ibox127) (computed denominator (FixedTape.midBox ibox127))
    (by decide +kernel)
private theorem midpoint_even_127 : ∀ k, 2 ∣ (ibox127 k).lo+(ibox127 k).hi := by decide +kernel
private theorem accepted_127 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox127) tree127 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox127 midpoint_even_127
  simp only [tree127,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox127,candidate_valid h (FixedTape.midBox ibox127),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox127 106 (FixedTape.rowsAux denominator ibox127 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox127) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_127
private noncomputable def tree126 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree127 tree128
attribute [irreducible] tree126
private theorem accepted_126 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox126) tree126 = true := by
  simp only [tree126,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox126 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox126 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_127 h,accepted_128 h⟩
private noncomputable def tree125 : TapeTree := .split 2 (((23441902230356533097993478221745677417511850371753452084678309933054517754508746953871160298700800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree126 tree129
attribute [irreducible] tree125
private theorem accepted_125 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox125) tree125 = true := by
  simp only [tree125,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox125 2 (23441902230356533097993478221745677417511850371753452084678309933054517754508746953871160298700800000000000000000000000 : Int) false,decode_split denominator ibox125 2 (23441902230356533097993478221745677417511850371753452084678309933054517754508746953871160298700800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_126 h,accepted_129 h⟩
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
private noncomputable def tree122 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree123 tree124
attribute [irreducible] tree122
private theorem accepted_122 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox122) tree122 = true := by
  simp only [tree122,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox122 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox122 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_123 h,accepted_124 h⟩
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
private noncomputable def tree119 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree120 tree121
attribute [irreducible] tree119
private theorem accepted_119 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox119) tree119 = true := by
  simp only [tree119,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox119 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox119 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_120 h,accepted_121 h⟩
private noncomputable def tree118 : TapeTree := .split 3 (((4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree119 tree122
attribute [irreducible] tree118
private theorem accepted_118 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox118) tree118 = true := by
  simp only [tree118,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox118 3 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) false,decode_split denominator ibox118 3 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_119 h,accepted_122 h⟩
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
private noncomputable def tree116 : TapeTree := .centered (candidateRows ibox116) (candidateRows (FixedTape.midBox ibox116))
attribute [irreducible] tree116
private theorem sign_116 : 2*denominator*(computed denominator (FixedTape.midBox ibox116)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox116).gradient k).lo.natAbs ((computed denominator ibox116).gradient k).hi.natAbs : Int)*((ibox116 k).hi-(ibox116 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox116
    (computed denominator ibox116) (computed denominator (FixedTape.midBox ibox116))
    (by decide +kernel)
private theorem midpoint_even_116 : ∀ k, 2 ∣ (ibox116 k).lo+(ibox116 k).hi := by decide +kernel
private theorem accepted_116 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox116) tree116 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox116 midpoint_even_116
  simp only [tree116,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox116,candidate_valid h (FixedTape.midBox ibox116),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox116 106 (FixedTape.rowsAux denominator ibox116 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox116) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_116
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
private noncomputable def tree114 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree115 tree116
attribute [irreducible] tree114
private theorem accepted_114 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox114) tree114 = true := by
  simp only [tree114,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox114 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox114 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_115 h,accepted_116 h⟩
private noncomputable def tree113 : TapeTree := .split 3 (((4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree114 tree117
attribute [irreducible] tree113
private theorem accepted_113 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox113) tree113 = true := by
  simp only [tree113,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox113 3 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) false,decode_split denominator ibox113 3 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_114 h,accepted_117 h⟩
private noncomputable def tree112 : TapeTree := .split 2 (((23441902230356533097993478221745677417511850371753452084678309933054517754508746953871160298700800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree113 tree118
attribute [irreducible] tree112
private theorem accepted_112 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox112) tree112 = true := by
  simp only [tree112,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox112 2 (23441902230356533097993478221745677417511850371753452084678309933054517754508746953871160298700800000000000000000000000 : Int) false,decode_split denominator ibox112 2 (23441902230356533097993478221745677417511850371753452084678309933054517754508746953871160298700800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_113 h,accepted_118 h⟩
private noncomputable def tree111 : TapeTree := .split 3 (((8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree112 tree125
attribute [irreducible] tree111
private theorem accepted_111 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox111) tree111 = true := by
  simp only [tree111,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox111 3 (8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) false,decode_split denominator ibox111 3 (8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_112 h,accepted_125 h⟩
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
private noncomputable def tree108 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree109 tree110
attribute [irreducible] tree108
private theorem accepted_108 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox108) tree108 = true := by
  simp only [tree108,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox108 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox108 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
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
private noncomputable def tree105 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree106 tree107
attribute [irreducible] tree105
private theorem accepted_105 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox105) tree105 = true := by
  simp only [tree105,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox105 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox105 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_106 h,accepted_107 h⟩
private noncomputable def tree104 : TapeTree := .split 2 (((19179738188473527080176482181428281523418786667798278978373162672499150890052611144076403880755200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree105 tree108
attribute [irreducible] tree104
private theorem accepted_104 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox104) tree104 = true := by
  simp only [tree104,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox104 2 (19179738188473527080176482181428281523418786667798278978373162672499150890052611144076403880755200000000000000000000000 : Int) false,decode_split denominator ibox104 2 (19179738188473527080176482181428281523418786667798278978373162672499150890052611144076403880755200000000000000000000000 : Int) true]
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
private noncomputable def tree100 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree101 tree102
attribute [irreducible] tree100
private theorem accepted_100 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox100) tree100 = true := by
  simp only [tree100,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox100 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox100 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_101 h,accepted_102 h⟩
private noncomputable def tree99 : TapeTree := .split 3 (((4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree100 tree103
attribute [irreducible] tree99
private theorem accepted_99 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox99) tree99 = true := by
  simp only [tree99,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox99 3 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) false,decode_split denominator ibox99 3 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_100 h,accepted_103 h⟩
private noncomputable def tree98 : TapeTree := .centered (candidateRows ibox98) (candidateRows (FixedTape.midBox ibox98))
attribute [irreducible] tree98
private theorem sign_98 : 2*denominator*(computed denominator (FixedTape.midBox ibox98)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox98).gradient k).lo.natAbs ((computed denominator ibox98).gradient k).hi.natAbs : Int)*((ibox98 k).hi-(ibox98 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox98
    (computed denominator ibox98) (computed denominator (FixedTape.midBox ibox98))
    (by decide +kernel)
private theorem midpoint_even_98 : ∀ k, 2 ∣ (ibox98 k).lo+(ibox98 k).hi := by decide +kernel
private theorem accepted_98 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox98) tree98 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox98 midpoint_even_98
  simp only [tree98,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox98,candidate_valid h (FixedTape.midBox ibox98),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox98 106 (FixedTape.rowsAux denominator ibox98 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox98) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_98
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
private noncomputable def tree96 : TapeTree := .split 3 (((4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree97 tree98
attribute [irreducible] tree96
private theorem accepted_96 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox96) tree96 = true := by
  simp only [tree96,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox96 3 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) false,decode_split denominator ibox96 3 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_97 h,accepted_98 h⟩
private noncomputable def tree95 : TapeTree := .split 2 (((19179738188473527080176482181428281523418786667798278978373162672499150890052611144076403880755200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree96 tree99
attribute [irreducible] tree95
private theorem accepted_95 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox95) tree95 = true := by
  simp only [tree95,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox95 2 (19179738188473527080176482181428281523418786667798278978373162672499150890052611144076403880755200000000000000000000000 : Int) false,decode_split denominator ibox95 2 (19179738188473527080176482181428281523418786667798278978373162672499150890052611144076403880755200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_96 h,accepted_99 h⟩
private noncomputable def tree94 : TapeTree := .split 3 (((8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree95 tree104
attribute [irreducible] tree94
private theorem accepted_94 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox94) tree94 = true := by
  simp only [tree94,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox94 3 (8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) false,decode_split denominator ibox94 3 (8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_95 h,accepted_104 h⟩
private noncomputable def tree93 : TapeTree := .split 2 (((21310820209415030089084980201586979470465318519775865531525736302776834322280679048973782089728000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree94 tree111
attribute [irreducible] tree93
private theorem accepted_93 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox93) tree93 = true := by
  simp only [tree93,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox93 2 (21310820209415030089084980201586979470465318519775865531525736302776834322280679048973782089728000000000000000000000000 : Int) false,decode_split denominator ibox93 2 (21310820209415030089084980201586979470465318519775865531525736302776834322280679048973782089728000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_94 h,accepted_111 h⟩
private noncomputable def tree92 : TapeTree := .split 3 (((17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree93 tree132
attribute [irreducible] tree92
private theorem accepted_92 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox92) tree92 = true := by
  simp only [tree92,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox92 3 (17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) false,decode_split denominator ibox92 3 (17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_93 h,accepted_132 h⟩
private noncomputable def tree91 : TapeTree := .split 2 (((25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree92 tree163
attribute [irreducible] tree91
private theorem accepted_91 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox91) tree91 = true := by
  simp only [tree91,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox91 2 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) false,decode_split denominator ibox91 2 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_92 h,accepted_163 h⟩
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
private noncomputable def tree88 : TapeTree := .split 2 (((14917574146590521062359486141110885629325722963843105872068015411943784025596475334281647462809600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree89 tree90
attribute [irreducible] tree88
private theorem accepted_88 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox88) tree88 = true := by
  simp only [tree88,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox88 2 (14917574146590521062359486141110885629325722963843105872068015411943784025596475334281647462809600000000000000000000000 : Int) false,decode_split denominator ibox88 2 (14917574146590521062359486141110885629325722963843105872068015411943784025596475334281647462809600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_89 h,accepted_90 h⟩
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
private noncomputable def tree85 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree86 tree87
attribute [irreducible] tree85
private theorem accepted_85 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox85) tree85 = true := by
  simp only [tree85,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox85 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox85 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_86 h,accepted_87 h⟩
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
private noncomputable def tree82 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree83 tree84
attribute [irreducible] tree82
private theorem accepted_82 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox82) tree82 = true := by
  simp only [tree82,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox82 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox82 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_83 h,accepted_84 h⟩
private noncomputable def tree81 : TapeTree := .split 2 (((14917574146590521062359486141110885629325722963843105872068015411943784025596475334281647462809600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree82 tree85
attribute [irreducible] tree81
private theorem accepted_81 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox81) tree81 = true := by
  simp only [tree81,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox81 2 (14917574146590521062359486141110885629325722963843105872068015411943784025596475334281647462809600000000000000000000000 : Int) false,decode_split denominator ibox81 2 (14917574146590521062359486141110885629325722963843105872068015411943784025596475334281647462809600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_82 h,accepted_85 h⟩
private noncomputable def tree80 : TapeTree := .split 3 (((25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree81 tree88
attribute [irreducible] tree80
private theorem accepted_80 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox80) tree80 = true := by
  simp only [tree80,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox80 3 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) false,decode_split denominator ibox80 3 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_81 h,accepted_88 h⟩
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
private noncomputable def tree77 : TapeTree := .split 3 (((25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree78 tree79
attribute [irreducible] tree77
private theorem accepted_77 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox77) tree77 = true := by
  simp only [tree77,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox77 3 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) false,decode_split denominator ibox77 3 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_78 h,accepted_79 h⟩
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
private noncomputable def tree75 : TapeTree := .centered (candidateRows ibox75) (candidateRows (FixedTape.midBox ibox75))
attribute [irreducible] tree75
private theorem sign_75 : 2*denominator*(computed denominator (FixedTape.midBox ibox75)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox75).gradient k).lo.natAbs ((computed denominator ibox75).gradient k).hi.natAbs : Int)*((ibox75 k).hi-(ibox75 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox75
    (computed denominator ibox75) (computed denominator (FixedTape.midBox ibox75))
    (by decide +kernel)
private theorem midpoint_even_75 : ∀ k, 2 ∣ (ibox75 k).lo+(ibox75 k).hi := by decide +kernel
private theorem accepted_75 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox75) tree75 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox75 midpoint_even_75
  simp only [tree75,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox75,candidate_valid h (FixedTape.midBox ibox75),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox75 106 (FixedTape.rowsAux denominator ibox75 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox75) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_75
private noncomputable def tree74 : TapeTree := .split 3 (((25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree75 tree76
attribute [irreducible] tree74
private theorem accepted_74 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox74) tree74 = true := by
  simp only [tree74,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox74 3 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) false,decode_split denominator ibox74 3 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_75 h,accepted_76 h⟩
private noncomputable def tree73 : TapeTree := .split 2 (((10655410104707515044542490100793489735232659259887932765762868151388417161140339524486891044864000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree74 tree77
attribute [irreducible] tree73
private theorem accepted_73 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox73) tree73 = true := by
  simp only [tree73,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox73 2 (10655410104707515044542490100793489735232659259887932765762868151388417161140339524486891044864000000000000000000000000 : Int) false,decode_split denominator ibox73 2 (10655410104707515044542490100793489735232659259887932765762868151388417161140339524486891044864000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_74 h,accepted_77 h⟩
private noncomputable def tree72 : TapeTree := .split 2 (((12786492125649018053450988120952187682279191111865519318915441781666100593368407429384269253836800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree73 tree80
attribute [irreducible] tree72
private theorem accepted_72 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox72) tree72 = true := by
  simp only [tree72,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox72 2 (12786492125649018053450988120952187682279191111865519318915441781666100593368407429384269253836800000000000000000000000 : Int) false,decode_split denominator ibox72 2 (12786492125649018053450988120952187682279191111865519318915441781666100593368407429384269253836800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_73 h,accepted_80 h⟩
private noncomputable def tree71 : TapeTree := .centered (candidateRows ibox71) (candidateRows (FixedTape.midBox ibox71))
attribute [irreducible] tree71
private theorem sign_71 : 2*denominator*(computed denominator (FixedTape.midBox ibox71)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox71).gradient k).lo.natAbs ((computed denominator ibox71).gradient k).hi.natAbs : Int)*((ibox71 k).hi-(ibox71 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox71
    (computed denominator ibox71) (computed denominator (FixedTape.midBox ibox71))
    (by decide +kernel)
private theorem midpoint_even_71 : ∀ k, 2 ∣ (ibox71 k).lo+(ibox71 k).hi := by decide +kernel
private theorem accepted_71 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox71) tree71 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox71 midpoint_even_71
  simp only [tree71,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox71,candidate_valid h (FixedTape.midBox ibox71),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox71 106 (FixedTape.rowsAux denominator ibox71 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox71) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_71
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
private noncomputable def tree69 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree70 tree71
attribute [irreducible] tree69
private theorem accepted_69 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox69) tree69 = true := by
  simp only [tree69,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox69 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox69 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_70 h,accepted_71 h⟩
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
private noncomputable def tree66 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree67 tree68
attribute [irreducible] tree66
private theorem accepted_66 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox66) tree66 = true := by
  simp only [tree66,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox66 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox66 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_67 h,accepted_68 h⟩
private noncomputable def tree65 : TapeTree := .split 2 (((14917574146590521062359486141110885629325722963843105872068015411943784025596475334281647462809600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree66 tree69
attribute [irreducible] tree65
private theorem accepted_65 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox65) tree65 = true := by
  simp only [tree65,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox65 2 (14917574146590521062359486141110885629325722963843105872068015411943784025596475334281647462809600000000000000000000000 : Int) false,decode_split denominator ibox65 2 (14917574146590521062359486141110885629325722963843105872068015411943784025596475334281647462809600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_66 h,accepted_69 h⟩
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
private noncomputable def tree62 : TapeTree := .split 3 (((4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree63 tree64
attribute [irreducible] tree62
private theorem accepted_62 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox62) tree62 = true := by
  simp only [tree62,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox62 3 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) false,decode_split denominator ibox62 3 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_63 h,accepted_64 h⟩
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
private noncomputable def tree59 : TapeTree := .split 3 (((4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree60 tree61
attribute [irreducible] tree59
private theorem accepted_59 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox59) tree59 = true := by
  simp only [tree59,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox59 3 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) false,decode_split denominator ibox59 3 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_60 h,accepted_61 h⟩
private noncomputable def tree58 : TapeTree := .split 2 (((14917574146590521062359486141110885629325722963843105872068015411943784025596475334281647462809600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree59 tree62
attribute [irreducible] tree58
private theorem accepted_58 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox58) tree58 = true := by
  simp only [tree58,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox58 2 (14917574146590521062359486141110885629325722963843105872068015411943784025596475334281647462809600000000000000000000000 : Int) false,decode_split denominator ibox58 2 (14917574146590521062359486141110885629325722963843105872068015411943784025596475334281647462809600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_59 h,accepted_62 h⟩
private noncomputable def tree57 : TapeTree := .split 3 (((8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree58 tree65
attribute [irreducible] tree57
private theorem accepted_57 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox57) tree57 = true := by
  simp only [tree57,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox57 3 (8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) false,decode_split denominator ibox57 3 (8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_58 h,accepted_65 h⟩
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
private noncomputable def tree54 : TapeTree := .split 0 (((18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) : ℚ)/(denominator : ℚ)) tree55 tree56
attribute [irreducible] tree54
private theorem accepted_54 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox54) tree54 = true := by
  simp only [tree54,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox54 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) false,decode_split denominator ibox54 0 (18291787346414566356554196837560552627617120978168712823075935938503954445251646702271332438713650721398288547840000000 : Int) true]
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
private noncomputable def tree52 : TapeTree := .split 2 (((10655410104707515044542490100793489735232659259887932765762868151388417161140339524486891044864000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree53 tree54
attribute [irreducible] tree52
private theorem accepted_52 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox52) tree52 = true := by
  simp only [tree52,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox52 2 (10655410104707515044542490100793489735232659259887932765762868151388417161140339524486891044864000000000000000000000000 : Int) false,decode_split denominator ibox52 2 (10655410104707515044542490100793489735232659259887932765762868151388417161140339524486891044864000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_53 h,accepted_54 h⟩
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
private noncomputable def tree49 : TapeTree := .split 3 (((4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree50 tree51
attribute [irreducible] tree49
private theorem accepted_49 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox49) tree49 = true := by
  simp only [tree49,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox49 3 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) false,decode_split denominator ibox49 3 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_50 h,accepted_51 h⟩
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
private noncomputable def tree46 : TapeTree := .split 3 (((4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree47 tree48
attribute [irreducible] tree46
private theorem accepted_46 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox46) tree46 = true := by
  simp only [tree46,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox46 3 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) false,decode_split denominator ibox46 3 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_47 h,accepted_48 h⟩
private noncomputable def tree45 : TapeTree := .split 2 (((10655410104707515044542490100793489735232659259887932765762868151388417161140339524486891044864000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree46 tree49
attribute [irreducible] tree45
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox45 2 (10655410104707515044542490100793489735232659259887932765762868151388417161140339524486891044864000000000000000000000000 : Int) false,decode_split denominator ibox45 2 (10655410104707515044542490100793489735232659259887932765762868151388417161140339524486891044864000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_46 h,accepted_49 h⟩
private noncomputable def tree44 : TapeTree := .split 3 (((8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree45 tree52
attribute [irreducible] tree44
private theorem accepted_44 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox44) tree44 = true := by
  simp only [tree44,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox44 3 (8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) false,decode_split denominator ibox44 3 (8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_45 h,accepted_52 h⟩
private noncomputable def tree43 : TapeTree := .split 2 (((12786492125649018053450988120952187682279191111865519318915441781666100593368407429384269253836800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree44 tree57
attribute [irreducible] tree43
private theorem accepted_43 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox43) tree43 = true := by
  simp only [tree43,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox43 2 (12786492125649018053450988120952187682279191111865519318915441781666100593368407429384269253836800000000000000000000000 : Int) false,decode_split denominator ibox43 2 (12786492125649018053450988120952187682279191111865519318915441781666100593368407429384269253836800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_44 h,accepted_57 h⟩
private noncomputable def tree42 : TapeTree := .split 3 (((17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree43 tree72
attribute [irreducible] tree42
private theorem accepted_42 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox42) tree42 = true := by
  simp only [tree42,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox42 3 (17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) false,decode_split denominator ibox42 3 (17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_43 h,accepted_72 h⟩
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
private noncomputable def tree39 : TapeTree := .split 3 (((25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree40 tree41
attribute [irreducible] tree39
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox39 3 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) false,decode_split denominator ibox39 3 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_40 h,accepted_41 h⟩
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
private noncomputable def tree37 : TapeTree := .centered (candidateRows ibox37) (candidateRows (FixedTape.midBox ibox37))
attribute [irreducible] tree37
private theorem sign_37 : 2*denominator*(computed denominator (FixedTape.midBox ibox37)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox37).gradient k).lo.natAbs ((computed denominator ibox37).gradient k).hi.natAbs : Int)*((ibox37 k).hi-(ibox37 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox37
    (computed denominator ibox37) (computed denominator (FixedTape.midBox ibox37))
    (by decide +kernel)
private theorem midpoint_even_37 : ∀ k, 2 ∣ (ibox37 k).lo+(ibox37 k).hi := by decide +kernel
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox37 midpoint_even_37
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox37,candidate_valid h (FixedTape.midBox ibox37),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox37 106 (FixedTape.rowsAux denominator ibox37 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox37) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_37
private noncomputable def tree36 : TapeTree := .split 3 (((25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree37 tree38
attribute [irreducible] tree36
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox36 3 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) false,decode_split denominator ibox36 3 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_37 h,accepted_38 h⟩
private noncomputable def tree35 : TapeTree := .split 2 (((6393246062824509026725494060476093841139595555932759659457720890833050296684203714692134626918400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree36 tree39
attribute [irreducible] tree35
private theorem accepted_35 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox35) tree35 = true := by
  simp only [tree35,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox35 2 (6393246062824509026725494060476093841139595555932759659457720890833050296684203714692134626918400000000000000000000000 : Int) false,decode_split denominator ibox35 2 (6393246062824509026725494060476093841139595555932759659457720890833050296684203714692134626918400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_36 h,accepted_39 h⟩
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
private noncomputable def tree31 : TapeTree := .split 2 (((7458787073295260531179743070555442814662861481921552936034007705971892012798237667140823731404800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree32 tree33
attribute [irreducible] tree31
private theorem accepted_31 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox31) tree31 = true := by
  simp only [tree31,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox31 2 (7458787073295260531179743070555442814662861481921552936034007705971892012798237667140823731404800000000000000000000000 : Int) false,decode_split denominator ibox31 2 (7458787073295260531179743070555442814662861481921552936034007705971892012798237667140823731404800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_32 h,accepted_33 h⟩
private noncomputable def tree30 : TapeTree := .split 3 (((8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree31 tree34
attribute [irreducible] tree30
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox30 3 (8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) false,decode_split denominator ibox30 3 (8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) true]
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
private noncomputable def tree27 : TapeTree := .split 3 (((8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree28 tree29
attribute [irreducible] tree27
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox27 3 (8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) false,decode_split denominator ibox27 3 (8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_28 h,accepted_29 h⟩
private noncomputable def tree26 : TapeTree := .split 2 (((6393246062824509026725494060476093841139595555932759659457720890833050296684203714692134626918400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree27 tree30
attribute [irreducible] tree26
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox26 2 (6393246062824509026725494060476093841139595555932759659457720890833050296684203714692134626918400000000000000000000000 : Int) false,decode_split denominator ibox26 2 (6393246062824509026725494060476093841139595555932759659457720890833050296684203714692134626918400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_27 h,accepted_30 h⟩
private noncomputable def tree25 : TapeTree := .split 3 (((17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree26 tree35
attribute [irreducible] tree25
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox25 3 (17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) false,decode_split denominator ibox25 3 (17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_26 h,accepted_35 h⟩
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
private noncomputable def tree22 : TapeTree := .split 3 (((25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree23 tree24
attribute [irreducible] tree22
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox22 3 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) false,decode_split denominator ibox22 3 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_23 h,accepted_24 h⟩
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
private noncomputable def tree20 : TapeTree := .split 2 (((2131082020941503008908498020158697947046531851977586553152573630277683432228067904897378208972800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree21 tree22
attribute [irreducible] tree20
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox20 2 (2131082020941503008908498020158697947046531851977586553152573630277683432228067904897378208972800000000000000000000000 : Int) false,decode_split denominator ibox20 2 (2131082020941503008908498020158697947046531851977586553152573630277683432228067904897378208972800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_21 h,accepted_22 h⟩
private noncomputable def tree19 : TapeTree := .centered (candidateRows ibox19) (candidateRows (FixedTape.midBox ibox19))
attribute [irreducible] tree19
private theorem sign_19 : 2*denominator*(computed denominator (FixedTape.midBox ibox19)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox19).gradient k).lo.natAbs ((computed denominator ibox19).gradient k).hi.natAbs : Int)*((ibox19 k).hi-(ibox19 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox19
    (computed denominator ibox19) (computed denominator (FixedTape.midBox ibox19))
    (by decide +kernel)
private theorem midpoint_even_19 : ∀ k, 2 ∣ (ibox19 k).lo+(ibox19 k).hi := by decide +kernel
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox19 midpoint_even_19
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox19,candidate_valid h (FixedTape.midBox ibox19),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox19 106 (FixedTape.rowsAux denominator ibox19 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox19) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_19
private noncomputable def tree18 : TapeTree := .centered (candidateRows ibox18) (candidateRows (FixedTape.midBox ibox18))
attribute [irreducible] tree18
private theorem sign_18 : 2*denominator*(computed denominator (FixedTape.midBox ibox18)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox18).gradient k).lo.natAbs ((computed denominator ibox18).gradient k).hi.natAbs : Int)*((ibox18 k).hi-(ibox18 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox18
    (computed denominator ibox18) (computed denominator (FixedTape.midBox ibox18))
    (by decide +kernel)
private theorem midpoint_even_18 : ∀ k, 2 ∣ (ibox18 k).lo+(ibox18 k).hi := by decide +kernel
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox18 midpoint_even_18
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox18,candidate_valid h (FixedTape.midBox ibox18),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox18 106 (FixedTape.rowsAux denominator ibox18 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox18) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_18
private noncomputable def tree17 : TapeTree := .split 3 (((8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree18 tree19
attribute [irreducible] tree17
private theorem accepted_17 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox17) tree17 = true := by
  simp only [tree17,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox17 3 (8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) false,decode_split denominator ibox17 3 (8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_18 h,accepted_19 h⟩
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
private noncomputable def tree15 : TapeTree := .centered (candidateRows ibox15) (candidateRows (FixedTape.midBox ibox15))
attribute [irreducible] tree15
private theorem sign_15 : 2*denominator*(computed denominator (FixedTape.midBox ibox15)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox15).gradient k).lo.natAbs ((computed denominator ibox15).gradient k).hi.natAbs : Int)*((ibox15 k).hi-(ibox15 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox15
    (computed denominator ibox15) (computed denominator (FixedTape.midBox ibox15))
    (by decide +kernel)
private theorem midpoint_even_15 : ∀ k, 2 ∣ (ibox15 k).lo+(ibox15 k).hi := by decide +kernel
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox15 midpoint_even_15
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox15,candidate_valid h (FixedTape.midBox ibox15),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox15 106 (FixedTape.rowsAux denominator ibox15 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox15) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_15
private noncomputable def tree14 : TapeTree := .split 3 (((8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree15 tree16
attribute [irreducible] tree14
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox14 3 (8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) false,decode_split denominator ibox14 3 (8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_15 h,accepted_16 h⟩
private noncomputable def tree13 : TapeTree := .split 2 (((2131082020941503008908498020158697947046531851977586553152573630277683432228067904897378208972800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree14 tree17
attribute [irreducible] tree13
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox13 2 (2131082020941503008908498020158697947046531851977586553152573630277683432228067904897378208972800000000000000000000000 : Int) false,decode_split denominator ibox13 2 (2131082020941503008908498020158697947046531851977586553152573630277683432228067904897378208972800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_14 h,accepted_17 h⟩
private noncomputable def tree12 : TapeTree := .split 3 (((17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree13 tree20
attribute [irreducible] tree12
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox12 3 (17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) false,decode_split denominator ibox12 3 (17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_13 h,accepted_20 h⟩
private noncomputable def tree11 : TapeTree := .split 2 (((4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree12 tree25
attribute [irreducible] tree11
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox11 2 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) false,decode_split denominator ibox11 2 (4262164041883006017816996040317395894093063703955173106305147260555366864456135809794756417945600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_12 h,accepted_25 h⟩
private noncomputable def tree10 : TapeTree := .split 2 (((8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree11 tree42
attribute [irreducible] tree10
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox10 2 (8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) false,decode_split denominator ibox10 2 (8524328083766012035633992080634791788186127407910346212610294521110733728912271619589512835891200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_11 h,accepted_42 h⟩
private noncomputable def tree9 : TapeTree := .split 2 (((17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree10 tree91
attribute [irreducible] tree9
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox9 2 (17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) false,decode_split denominator ibox9 2 (17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_10 h,accepted_91 h⟩
private noncomputable def tree8 : TapeTree := .face 1 true (candidateRows ibox8) tree9
attribute [irreducible] tree8
private theorem sign_8 : 0 ≤ ((computed denominator ibox8).gradient 1).lo := by decide +kernel
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox8,?_,accepted_9 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox8)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox8).gradient 1).lo) denominator_positive).2 sign_8
private noncomputable def tree7 : TapeTree := .centered (candidateRows ibox7) (candidateRows (FixedTape.midBox ibox7))
attribute [irreducible] tree7
private theorem sign_7 : 2*denominator*(computed denominator (FixedTape.midBox ibox7)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox7).gradient k).lo.natAbs ((computed denominator ibox7).gradient k).hi.natAbs : Int)*((ibox7 k).hi-(ibox7 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox7
    (computed denominator ibox7) (computed denominator (FixedTape.midBox ibox7))
    (by decide +kernel)
private theorem midpoint_even_7 : ∀ k, 2 ∣ (ibox7 k).lo+(ibox7 k).hi := by decide +kernel
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox7 midpoint_even_7
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox7,candidate_valid h (FixedTape.midBox ibox7),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox7 106 (FixedTape.rowsAux denominator ibox7 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox7) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_7
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
private noncomputable def tree5 : TapeTree := .split 2 (((17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree6 tree7
attribute [irreducible] tree5
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox5 2 (17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) false,decode_split denominator ibox5 2 (17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_6 h,accepted_7 h⟩
private noncomputable def tree4 : TapeTree := .face 1 true (candidateRows ibox4) tree5
attribute [irreducible] tree4
private theorem sign_4 : 0 ≤ ((computed denominator ibox4).gradient 1).lo := by decide +kernel
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox4,?_,accepted_5 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox4)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox4).gradient 1).lo) denominator_positive).2 sign_4
private noncomputable def tree3 : TapeTree := .split 1 (((25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree8
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) false,decode_split denominator ibox3 1 (25572984251298036106901976241904375364558382223731038637830883563332201186736814858768538507673600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_8 h⟩
private noncomputable def tree2 : TapeTree := .direct (candidateRows ibox2)
attribute [irreducible] tree2
private theorem sign_2 : (computed denominator ibox2).value.hi ≤ 0 := by decide +kernel
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox2,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox2).value.hi denominator_positive).1 sign_2
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
private noncomputable def tree0 : TapeTree := .split 1 (((17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree1 tree3
attribute [irreducible] tree0
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox0 1 (17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) false,decode_split denominator ibox0 1 (17048656167532024071267984161269583576372254815820692425220589042221467457824543239179025671782400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_1 h,accepted_3 h⟩
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (17/32 : ℚ) (2708333333333333/5000000000000000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 106 = e112 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (17/32 : ℚ) (2708333333333333/5000000000000000 : ℚ)) x → eval e112 x ≤ 0 := by
  have hb := h.child_4 tape 106 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell73_low_internal

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell73_low_internal
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((17/32 : ℚ) : ℝ) < p ∧ p ≤ ((2708333333333333/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 73 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 73 p)
    (hk0 : ((2708333333333333/5000000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((17/32 : ℚ) : ℝ))
    (hk1 : ((2708333333333333/5000000000000000 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((17/32 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell73_low_internal.cell_bound h.child_8 h.child_9 (Cell73_low_internal.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell73_low_internal
