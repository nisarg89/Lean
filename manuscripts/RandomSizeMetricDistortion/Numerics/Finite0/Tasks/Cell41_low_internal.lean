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
namespace Cell41_low_internal
private noncomputable def qValues : Fin 4 → ℚ := ![(60230906816313969030514572001339460978/89724550177542750564178380635883025977 : ℚ),(150347674543497050272330000000000000000/89724550177542750564178380635883025977 : ℚ),(212972282270594181467550798930654692480/91732889648507553341705521056564682001 : ℚ),(-69335384333710903332620000000000000000/91732889648507553341705521056564682001 : ℚ)]
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
    priceLambda 41 p = ((60230906816313969030514572001339460978/89724550177542750564178380635883025977 : ℝ)+(150347674543497050272330000000000000000/89724550177542750564178380635883025977 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell41,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 41 p = (((212972282270594181467550798930654692480/91732889648507553341705521056564682001 : ℝ)+(-69335384333710903332620000000000000000/91732889648507553341705521056564682001 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell41,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e114 x = (x 0*(1-x 0))*(aPoint x+priceLambda 41 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 41 (x 0)*psiStar (rPoint x)+(0)-(0)) := by
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
    (hL : lambdaStar (x 0) = priceLambda 41 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 41 (x 0)) :
    (1)*eval e114 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,if_pos hA,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (1/4 : ℚ) (13/50 : ℚ)) x → eval e114 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((1/4 : ℚ) : ℝ) < p ∧ p ≤ ((13/50 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 41 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 41 p)
    (hk0 : ((13/50 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((1/4 : ℚ) : ℝ))
    (hk1 : ((13/50 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((1/4 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h3 (1/4 : ℚ) (13/50 : ℚ) ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ) p a A r hpcell hk0 hk1 hr ha hap hpA hAr
  have hcut : ((13/50 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 41 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 41 (x 0) := by simpa only [hxp] using hT
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
.const (60230906816313969030514572001339460978/89724550177542750564178380635883025977 : ℚ),
.const (150347674543497050272330000000000000000/89724550177542750564178380635883025977 : ℚ),
.mul 74 1,
.add 73 75,
.const (212972282270594181467550798930654692480/91732889648507553341705521056564682001 : ℚ),
.const (-69335384333710903332620000000000000000/91732889648507553341705521056564682001 : ℚ),
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
private noncomputable def ssaQVals : Fin 16 → ℚ := ![(1/1 : ℚ),(49/100 : ℚ),(390189/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(60230906816313969030514572001339460978/89724550177542750564178380635883025977 : ℚ),(150347674543497050272330000000000000000/89724550177542750564178380635883025977 : ℚ),(212972282270594181467550798930654692480/91732889648507553341705521056564682001 : ℚ),(-69335384333710903332620000000000000000/91732889648507553341705521056564682001 : ℚ),(-145513/100000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
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
private noncomputable def denominator : Int := 3411913612079990756115012153836963584520594434363157947865668415962986890143490749108440885362688000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000,887097539140797596589903159997610531975354552934421066445073788150376591437307594768194630194298880000000⟩,⟨0,3411913612079990756115012153836963584520594434363157947865668415962986890143490749108440885362688000000000⟩,⟨0,3411913612079990756115012153836963584520594434363157947865668415962986890143490749108440885362688000000000⟩,⟨0,3411913612079990756115012153836963584520594434363157947865668415962986890143490749108440885362688000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := splitI ibox0 2 1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := splitI ibox1 1 1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := faceI ibox2 1 true
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 2 852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox3 2 852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 true
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox1 1 1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 true
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 2 852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := faceI ibox7 1 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox8 3 1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 false
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox8 3 1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 true
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox6 2 852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox11 1 2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 false
private noncomputable def ibox13 : Fin 4 → FixedTape.I := faceI ibox12 1 true
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox11 1 2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 true
private noncomputable def ibox15 : Fin 4 → FixedTape.I := faceI ibox14 1 true
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox15 3 1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 false
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox15 3 1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 true
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox0 2 1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox18 1 1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 false
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 2 2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox20 1 852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 false
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox20 1 852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 true
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox19 2 2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 true
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox23 2 2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 false
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox24 1 852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 false
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox24 1 852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 true
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox23 2 2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 true
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox27 1 852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 false
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox27 1 852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 true
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox18 1 1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 true
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox30 2 2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 false
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox31 1 2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 false
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox32 2 2132446007549994222571882596148102240325371521476973717416042759976866806339681718192775553351680000000000 false
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox32 2 2132446007549994222571882596148102240325371521476973717416042759976866806339681718192775553351680000000000 true
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox31 1 2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 true
private noncomputable def ibox36 : Fin 4 → FixedTape.I := splitI ibox35 3 1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 false
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox36 2 2132446007549994222571882596148102240325371521476973717416042759976866806339681718192775553351680000000000 false
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox36 2 2132446007549994222571882596148102240325371521476973717416042759976866806339681718192775553351680000000000 true
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox35 3 1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 true
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox39 2 2132446007549994222571882596148102240325371521476973717416042759976866806339681718192775553351680000000000 false
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox39 2 2132446007549994222571882596148102240325371521476973717416042759976866806339681718192775553351680000000000 true
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox30 2 2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 true
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox42 3 1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 false
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox43 1 2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 false
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox44 2 2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 false
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox44 2 2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 true
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox43 1 2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 true
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox47 2 2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 false
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox47 2 2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 true
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox42 3 1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 true
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox50 1 2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 false
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox51 2 2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 false
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox51 2 2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 true
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox50 1 2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 true
private noncomputable def ibox55 : Fin 4 → FixedTape.I := splitI ibox54 2 2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 false
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox54 2 2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 true
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
private noncomputable def tree54 : TapeTree := .split 2 (((2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 : Int) : ℚ)/(denominator : ℚ)) tree55 tree56
attribute [irreducible] tree54
private theorem accepted_54 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox54) tree54 = true := by
  simp only [tree54,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox54 2 (2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 : Int) false,decode_split denominator ibox54 2 (2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 : Int) true]
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
private noncomputable def tree51 : TapeTree := .split 2 (((2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 : Int) : ℚ)/(denominator : ℚ)) tree52 tree53
attribute [irreducible] tree51
private theorem accepted_51 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox51) tree51 = true := by
  simp only [tree51,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox51 2 (2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 : Int) false,decode_split denominator ibox51 2 (2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_52 h,accepted_53 h⟩
private noncomputable def tree50 : TapeTree := .split 1 (((2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 : Int) : ℚ)/(denominator : ℚ)) tree51 tree54
attribute [irreducible] tree50
private theorem accepted_50 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox50) tree50 = true := by
  simp only [tree50,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox50 1 (2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 : Int) false,decode_split denominator ibox50 1 (2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 : Int) true]
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
private noncomputable def tree47 : TapeTree := .split 2 (((2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 : Int) : ℚ)/(denominator : ℚ)) tree48 tree49
attribute [irreducible] tree47
private theorem accepted_47 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox47) tree47 = true := by
  simp only [tree47,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox47 2 (2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 : Int) false,decode_split denominator ibox47 2 (2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 : Int) true]
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
private noncomputable def tree45 : TapeTree := .centered (candidateRows ibox45) (candidateRows (FixedTape.midBox ibox45))
attribute [irreducible] tree45
private theorem sign_45 : 2*denominator*(computed denominator (FixedTape.midBox ibox45)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox45).gradient k).lo.natAbs ((computed denominator ibox45).gradient k).hi.natAbs : Int)*((ibox45 k).hi-(ibox45 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox45
    (computed denominator ibox45) (computed denominator (FixedTape.midBox ibox45))
    (by decide +kernel)
private theorem midpoint_even_45 : ∀ k, 2 ∣ (ibox45 k).lo+(ibox45 k).hi := by decide +kernel
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox45 midpoint_even_45
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox45,candidate_valid h (FixedTape.midBox ibox45),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox45 106 (FixedTape.rowsAux denominator ibox45 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox45) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_45
private noncomputable def tree44 : TapeTree := .split 2 (((2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 : Int) : ℚ)/(denominator : ℚ)) tree45 tree46
attribute [irreducible] tree44
private theorem accepted_44 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox44) tree44 = true := by
  simp only [tree44,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox44 2 (2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 : Int) false,decode_split denominator ibox44 2 (2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_45 h,accepted_46 h⟩
private noncomputable def tree43 : TapeTree := .split 1 (((2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 : Int) : ℚ)/(denominator : ℚ)) tree44 tree47
attribute [irreducible] tree43
private theorem accepted_43 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox43) tree43 = true := by
  simp only [tree43,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox43 1 (2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 : Int) false,decode_split denominator ibox43 1 (2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_44 h,accepted_47 h⟩
private noncomputable def tree42 : TapeTree := .split 3 (((1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) : ℚ)/(denominator : ℚ)) tree43 tree50
attribute [irreducible] tree42
private theorem accepted_42 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox42) tree42 = true := by
  simp only [tree42,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox42 3 (1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) false,decode_split denominator ibox42 3 (1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_43 h,accepted_50 h⟩
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
private noncomputable def tree39 : TapeTree := .split 2 (((2132446007549994222571882596148102240325371521476973717416042759976866806339681718192775553351680000000000 : Int) : ℚ)/(denominator : ℚ)) tree40 tree41
attribute [irreducible] tree39
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox39 2 (2132446007549994222571882596148102240325371521476973717416042759976866806339681718192775553351680000000000 : Int) false,decode_split denominator ibox39 2 (2132446007549994222571882596148102240325371521476973717416042759976866806339681718192775553351680000000000 : Int) true]
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
private noncomputable def tree36 : TapeTree := .split 2 (((2132446007549994222571882596148102240325371521476973717416042759976866806339681718192775553351680000000000 : Int) : ℚ)/(denominator : ℚ)) tree37 tree38
attribute [irreducible] tree36
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox36 2 (2132446007549994222571882596148102240325371521476973717416042759976866806339681718192775553351680000000000 : Int) false,decode_split denominator ibox36 2 (2132446007549994222571882596148102240325371521476973717416042759976866806339681718192775553351680000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_37 h,accepted_38 h⟩
private noncomputable def tree35 : TapeTree := .split 3 (((1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) : ℚ)/(denominator : ℚ)) tree36 tree39
attribute [irreducible] tree35
private theorem accepted_35 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox35) tree35 = true := by
  simp only [tree35,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox35 3 (1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) false,decode_split denominator ibox35 3 (1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) true]
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
private noncomputable def tree32 : TapeTree := .split 2 (((2132446007549994222571882596148102240325371521476973717416042759976866806339681718192775553351680000000000 : Int) : ℚ)/(denominator : ℚ)) tree33 tree34
attribute [irreducible] tree32
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox32 2 (2132446007549994222571882596148102240325371521476973717416042759976866806339681718192775553351680000000000 : Int) false,decode_split denominator ibox32 2 (2132446007549994222571882596148102240325371521476973717416042759976866806339681718192775553351680000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_33 h,accepted_34 h⟩
private noncomputable def tree31 : TapeTree := .split 1 (((2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 : Int) : ℚ)/(denominator : ℚ)) tree32 tree35
attribute [irreducible] tree31
private theorem accepted_31 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox31) tree31 = true := by
  simp only [tree31,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox31 1 (2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 : Int) false,decode_split denominator ibox31 1 (2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_32 h,accepted_35 h⟩
private noncomputable def tree30 : TapeTree := .split 2 (((2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 : Int) : ℚ)/(denominator : ℚ)) tree31 tree42
attribute [irreducible] tree30
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox30 2 (2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 : Int) false,decode_split denominator ibox30 2 (2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_31 h,accepted_42 h⟩
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
private noncomputable def tree27 : TapeTree := .split 1 (((852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 : Int) : ℚ)/(denominator : ℚ)) tree28 tree29
attribute [irreducible] tree27
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox27 1 (852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 : Int) false,decode_split denominator ibox27 1 (852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_28 h,accepted_29 h⟩
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
private noncomputable def tree24 : TapeTree := .split 1 (((852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 : Int) : ℚ)/(denominator : ℚ)) tree25 tree26
attribute [irreducible] tree24
private theorem accepted_24 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox24) tree24 = true := by
  simp only [tree24,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox24 1 (852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 : Int) false,decode_split denominator ibox24 1 (852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_25 h,accepted_26 h⟩
private noncomputable def tree23 : TapeTree := .split 2 (((2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 : Int) : ℚ)/(denominator : ℚ)) tree24 tree27
attribute [irreducible] tree23
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox23 2 (2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 : Int) false,decode_split denominator ibox23 2 (2985424410569991911600635634607343136455520130067763204382459863967613528875554405469885774692352000000000 : Int) true]
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
private noncomputable def tree20 : TapeTree := .split 1 (((852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 : Int) : ℚ)/(denominator : ℚ)) tree21 tree22
attribute [irreducible] tree20
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox20 1 (852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 : Int) false,decode_split denominator ibox20 1 (852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_21 h,accepted_22 h⟩
private noncomputable def tree19 : TapeTree := .split 2 (((2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree23
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 2 (2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 : Int) false,decode_split denominator ibox19 2 (2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_20 h,accepted_23 h⟩
private noncomputable def tree18 : TapeTree := .split 1 (((1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) : ℚ)/(denominator : ℚ)) tree19 tree30
attribute [irreducible] tree18
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox18 1 (1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) false,decode_split denominator ibox18 1 (1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_19 h,accepted_30 h⟩
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
private noncomputable def tree15 : TapeTree := .split 3 (((1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) : ℚ)/(denominator : ℚ)) tree16 tree17
attribute [irreducible] tree15
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox15 3 (1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) false,decode_split denominator ibox15 3 (1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) true]
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
private noncomputable def tree12 : TapeTree := .face 1 true (candidateRows ibox12) tree13
attribute [irreducible] tree12
private theorem sign_12 : 0 ≤ ((computed denominator ibox12).gradient 1).lo := by decide +kernel
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox12,?_,accepted_13 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox12)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox12).gradient 1).lo) denominator_positive).2 sign_12
private noncomputable def tree11 : TapeTree := .split 1 (((2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 : Int) : ℚ)/(denominator : ℚ)) tree12 tree14
attribute [irreducible] tree11
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox11 1 (2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 : Int) false,decode_split denominator ibox11 1 (2558935209059993067086259115377722688390445825772368460899251311972240167607618061831330664022016000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_12 h,accepted_14 h⟩
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
private noncomputable def tree8 : TapeTree := .split 3 (((1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) : ℚ)/(denominator : ℚ)) tree9 tree10
attribute [irreducible] tree8
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox8 3 (1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) false,decode_split denominator ibox8 3 (1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_9 h,accepted_10 h⟩
private noncomputable def tree7 : TapeTree := .face 1 true (candidateRows ibox7) tree8
attribute [irreducible] tree7
private theorem sign_7 : 0 ≤ ((computed denominator ibox7).gradient 1).lo := by decide +kernel
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox7,?_,accepted_8 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox7)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox7).gradient 1).lo) denominator_positive).2 sign_7
private noncomputable def tree6 : TapeTree := .split 2 (((852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree11
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 2 (852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 : Int) false,decode_split denominator ibox6 2 (852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_7 h,accepted_11 h⟩
private noncomputable def tree5 : TapeTree := .centered (candidateRows ibox5) (candidateRows (FixedTape.midBox ibox5))
attribute [irreducible] tree5
private theorem sign_5 : 2*denominator*(computed denominator (FixedTape.midBox ibox5)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox5).gradient k).lo.natAbs ((computed denominator ibox5).gradient k).hi.natAbs : Int)*((ibox5 k).hi-(ibox5 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox5
    (computed denominator ibox5) (computed denominator (FixedTape.midBox ibox5))
    (by decide +kernel)
private theorem midpoint_even_5 : ∀ k, 2 ∣ (ibox5 k).lo+(ibox5 k).hi := by decide +kernel
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox5 midpoint_even_5
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox5,candidate_valid h (FixedTape.midBox ibox5),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox5 106 (FixedTape.rowsAux denominator ibox5 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox5) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_5
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
private noncomputable def tree3 : TapeTree := .split 2 (((852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree5
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 2 (852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 : Int) false,decode_split denominator ibox3 2 (852978403019997689028753038459240896130148608590789486966417103990746722535872687277110221340672000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_5 h⟩
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
private noncomputable def tree1 : TapeTree := .split 1 (((1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) : ℚ)/(denominator : ℚ)) tree2 tree6
attribute [irreducible] tree1
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox1 1 (1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) false,decode_split denominator ibox1 1 (1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_2 h,accepted_6 h⟩
private noncomputable def tree0 : TapeTree := .split 2 (((1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) : ℚ)/(denominator : ℚ)) tree1 tree18
attribute [irreducible] tree0
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox0 2 (1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) false,decode_split denominator ibox0 2 (1705956806039995378057506076918481792260297217181578973932834207981493445071745374554220442681344000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_1 h,accepted_18 h⟩
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (1/4 : ℚ) (13/50 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 106 = e114 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (1/4 : ℚ) (13/50 : ℚ)) x → eval e114 x ≤ 0 := by
  have hb := h.child_4 tape 106 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell41_low_internal

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell41_low_internal
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((1/4 : ℚ) : ℝ) < p ∧ p ≤ ((13/50 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 41 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 41 p)
    (hk0 : ((13/50 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((1/4 : ℚ) : ℝ))
    (hk1 : ((13/50 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((1/4 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell41_low_internal.cell_bound h.child_8 h.child_9 (Cell41_low_internal.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell41_low_internal
