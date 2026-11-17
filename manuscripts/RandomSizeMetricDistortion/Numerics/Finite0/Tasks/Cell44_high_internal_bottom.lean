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
namespace Cell44_high_internal_bottom
private noncomputable def qValues : Fin 4 → ℚ := ![(11058151779627512315963344412245384228/16078071040076743804665765745415535483 : ℚ),(25942610050486363618522000000000000000/16078071040076743804665765745415535483 : ℚ),(1652902592170439205491658516673692736/708399878062304078364562450880948267 : ℚ),(-1699351161833095305680000000000000000/2125199634186912235093687352642844801 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics14.e2 qValues
private noncomputable abbrev e6 : PolyExpr := SharedFiniteSemantics14.e6 qValues
private noncomputable abbrev e11 : PolyExpr := SharedFiniteSemantics14.e11 qValues
private noncomputable abbrev e15 : PolyExpr := SharedFiniteSemantics14.e15 qValues
private noncomputable abbrev e17 : PolyExpr := SharedFiniteSemantics14.e17 qValues
private noncomputable abbrev e113 : PolyExpr := SharedFiniteSemantics14.e113 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics14.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics14.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics14.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics14.node_4 qValues
private noncomputable abbrev node_5 := SharedFiniteSemantics14.node_5 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics14.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics14.node_7 qValues
private noncomputable abbrev node_8 := SharedFiniteSemantics14.node_8 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics14.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics14.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics14.node_11 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics14.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics14.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics14.node_15 qValues
private noncomputable abbrev node_16 := SharedFiniteSemantics14.node_16 qValues
private noncomputable abbrev node_17 := SharedFiniteSemantics14.node_17 qValues
private noncomputable abbrev node_55 := SharedFiniteSemantics14.node_55 qValues
private noncomputable abbrev node_56 := SharedFiniteSemantics14.node_56 qValues
private noncomputable abbrev node_73 := SharedFiniteSemantics14.node_73 qValues
private noncomputable abbrev node_74 := SharedFiniteSemantics14.node_74 qValues
private noncomputable abbrev node_75 := SharedFiniteSemantics14.node_75 qValues
private noncomputable abbrev node_76 := SharedFiniteSemantics14.node_76 qValues
private noncomputable abbrev node_77 := SharedFiniteSemantics14.node_77 qValues
private noncomputable abbrev node_78 := SharedFiniteSemantics14.node_78 qValues
private noncomputable abbrev node_79 := SharedFiniteSemantics14.node_79 qValues
private noncomputable abbrev node_80 := SharedFiniteSemantics14.node_80 qValues
private noncomputable abbrev node_81 := SharedFiniteSemantics14.node_81 qValues
private noncomputable abbrev node_82 := SharedFiniteSemantics14.node_82 qValues
private noncomputable abbrev node_83 := SharedFiniteSemantics14.node_83 qValues
private noncomputable abbrev node_84 := SharedFiniteSemantics14.node_84 qValues
private noncomputable abbrev node_86 := SharedFiniteSemantics14.node_86 qValues
private noncomputable abbrev node_87 := SharedFiniteSemantics14.node_87 qValues
private noncomputable abbrev node_88 := SharedFiniteSemantics14.node_88 qValues
private noncomputable abbrev node_93 := SharedFiniteSemantics14.node_93 qValues
private noncomputable abbrev node_94 := SharedFiniteSemantics14.node_94 qValues
private noncomputable abbrev node_95 := SharedFiniteSemantics14.node_95 qValues
private noncomputable abbrev node_112 := SharedFiniteSemantics14.node_112 qValues
private noncomputable abbrev node_113 := SharedFiniteSemantics14.node_113 qValues
private noncomputable abbrev semantic_H_38 := SharedFiniteSemantics14.semantic_H_38 qValues
private noncomputable abbrev semantic_H_54 := SharedFiniteSemantics14.semantic_H_54 qValues
private noncomputable abbrev semantic_H_72 := SharedFiniteSemantics14.semantic_H_72 qValues
private noncomputable abbrev semantic_psi_111 := SharedFiniteSemantics14.semantic_psi_111 qValues
private noncomputable def aPoint (x : Fin 4 → ℝ) : ℝ := x 0*x 1
private noncomputable def rPoint (x : Fin 4 → ℝ) : ℝ := bStar+(1-bStar)*x 3
private noncomputable def capPoint (x : Fin 4 → ℝ) : ℝ := x 0+(bStar-x 0)*x 2
private noncomputable def yPoint (x : Fin 4 → ℝ) : ℝ := aPoint x+capPoint x-x 0
private theorem point_6 (x : Fin 4 → ℝ) : eval e6 x = aPoint x := by
  simp only [node_2,node_3,node_6] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_15 (x : Fin 4 → ℝ) : eval e15 x = rPoint x := by
  simp only [node_5,node_7,node_13,node_14,node_15] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_2 (x : Fin 4 → ℝ) : eval e2 x = x 0 := by
  simp only [node_2] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_11 (x : Fin 4 → ℝ) : eval e11 x = capPoint x := by
  simp only [node_2,node_4,node_7,node_8,node_9,node_10,node_11] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_17 (x : Fin 4 → ℝ) : eval e17 x = yPoint x := by
  simp only [node_2,node_3,node_4,node_6,node_7,node_8,node_9,node_10,node_11,node_16,node_17] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem price_lambda_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceLambda 44 p = ((11058151779627512315963344412245384228/16078071040076743804665765745415535483 : ℝ)+(25942610050486363618522000000000000000/16078071040076743804665765745415535483 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell44,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 44 p = (((1652902592170439205491658516673692736/708399878062304078364562450880948267 : ℝ)+(-1699351161833095305680000000000000000/2125199634186912235093687352642844801 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell44,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e113 x = (x 0*(1-x 0))*(aPoint x+priceLambda 44 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 44 (x 0)*psiStar (rPoint x)+(0)-(0)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_8,node_55,node_56,node_73,node_74,node_75,node_76,node_77,node_78,node_79,node_80,node_81,node_82,node_83,node_84,node_86,node_87,node_88,node_93,node_94,node_95,node_112,node_113,semantic_H_38,semantic_H_54,semantic_H_72,semantic_psi_111,point_6,point_15,point_2,point_11,point_17]
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
    (hL : lambdaStar (x 0) = priceLambda 44 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 44 (x 0)) :
    (1)*eval e113 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,if_pos hA,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (2708333333333333/10000000000000000 : ℚ) (9/32 : ℚ)) x → eval e113 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((2708333333333333/10000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((9/32 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 44 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 44 p)
    (hkb : ((9/32 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((2708333333333333/10000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : A ≤ bStar) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h6 (2708333333333333/10000000000000000 : ℚ) (9/32 : ℚ) bStar p a A r hpcell hkb hr ha hap hpA hcase
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 44 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 44 (x 0) := by simpa only [hxp] using hT
  have hAb : A ≤ bStar := hcase
  have hflag : aPoint x ≤ bStar := by rw [hax]; exact hap.trans (hpA.trans hAb)
  have hflagA : capPoint x ≤ bStar := by simpa only [hAx] using hAb
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e113 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
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
.mul 1 2,
.const (2840189/5000000 : ℚ),
.neg 1,
.add 6 7,
.mul 8 3,
.add 1 9,
.const (2159811/5000000 : ℚ),
.mul 11 4,
.add 6 12,
.add 5 10,
.add 14 7,
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
.mul 16 5,
.mul 5 5,
.mul 19 38,
.mul 5 38,
.mul 22 40,
.add 39 41,
.mul 38 38,
.mul 43 43,
.mul 44 44,
.mul 45 45,
.mul 5 46,
.mul 30 47,
.add 42 48,
.neg 49,
.add 37 50,
.mul 35 51,
.neg 52,
.add 36 53,
.mul 16 10,
.mul 10 10,
.mul 19 56,
.mul 10 56,
.mul 22 58,
.add 57 59,
.mul 56 56,
.mul 61 61,
.mul 62 62,
.mul 63 63,
.mul 10 64,
.mul 30 65,
.add 60 66,
.neg 67,
.add 55 68,
.mul 35 69,
.neg 70,
.add 54 71,
.const (11058151779627512315963344412245384228/16078071040076743804665765745415535483 : ℚ),
.const (25942610050486363618522000000000000000/16078071040076743804665765745415535483 : ℚ),
.mul 74 1,
.add 73 75,
.const (1652902592170439205491658516673692736/708399878062304078364562450880948267 : ℚ),
.const (-1699351161833095305680000000000000000/2125199634186912235093687352642844801 : ℚ),
.mul 78 1,
.add 77 79,
.add 0 7,
.mul 1 81,
.const (-145513/100000 : ℚ),
.add 80 83,
.mul 84 82,
.mul 5 82,
.mul 76 72,
.add 86 87,
.const (19/73 : ℚ),
.mul 89 13,
.mul 13 13,
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
private noncomputable def ssaQVals : Fin 16 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(2159811/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(11058151779627512315963344412245384228/16078071040076743804665765745415535483 : ℚ),(25942610050486363618522000000000000000/16078071040076743804665765745415535483 : ℚ),(1652902592170439205491658516673692736/708399878062304078364562450880948267 : ℚ),(-1699351161833095305680000000000000000/2125199634186912235093687352642844801 : ℚ),(-145513/100000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_3cb976fdfe9d7cf4.p107 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_3cb976fdfe9d7cf4.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 106 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_3cb976fdfe9d7cf4.ssa_matches ssaQVals D B

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
private noncomputable def denominator : Int := 2596789658753263879840777313277164502885039366028367479587843491177010635400714941918212207411200000000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨703297199245675547563888563903769391505454385727199429553728744581524394159577257535827959483368602726259752960000000,730347091524355466205218619359202516436417321695478353634080981893534241206451077414497183334400000000000000000000000⟩,⟨0,2596789658753263879840777313277164502885039366028367479587843491177010635400714941918212207411200000000000000000000000⟩,⟨0,2596789658753263879840777313277164502885039366028367479587843491177010635400714941918212207411200000000000000000000000⟩,⟨0,2596789658753263879840777313277164502885039366028367479587843491177010635400714941918212207411200000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 3 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := splitI ibox1 2 1298394829376631939920388656638582251442519683014183739793921745588505317700357470959106103705600000000000000000000000 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 1 1298394829376631939920388656638582251442519683014183739793921745588505317700357470959106103705600000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox2 1 1298394829376631939920388656638582251442519683014183739793921745588505317700357470959106103705600000000000000000000000 true
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 1 1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox4 1 1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 true
private noncomputable def ibox7 : Fin 4 → FixedTape.I := faceI ibox6 1 true
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox1 2 1298394829376631939920388656638582251442519683014183739793921745588505317700357470959106103705600000000000000000000000 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox8 1 1298394829376631939920388656638582251442519683014183739793921745588505317700357470959106103705600000000000000000000000 false
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox9 2 1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 false
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox9 2 1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox8 1 1298394829376631939920388656638582251442519683014183739793921745588505317700357470959106103705600000000000000000000000 true
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox12 2 1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 false
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox13 1 1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 false
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox13 1 1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 true
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox12 2 1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 true
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 1 1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox16 1 1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 true
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
private noncomputable def tree16 : TapeTree := .split 1 (((1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree18
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 1 (1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 : Int) false,decode_split denominator ibox16 1 (1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_17 h,accepted_18 h⟩
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
private noncomputable def tree14 : TapeTree := .centered (candidateRows ibox14) (candidateRows (FixedTape.midBox ibox14))
attribute [irreducible] tree14
private theorem sign_14 : 2*denominator*(computed denominator (FixedTape.midBox ibox14)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox14).gradient k).lo.natAbs ((computed denominator ibox14).gradient k).hi.natAbs : Int)*((ibox14 k).hi-(ibox14 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox14
    (computed denominator ibox14) (computed denominator (FixedTape.midBox ibox14))
    (by decide +kernel)
private theorem midpoint_even_14 : ∀ k, 2 ∣ (ibox14 k).lo+(ibox14 k).hi := by decide +kernel
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox14 midpoint_even_14
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox14,candidate_valid h (FixedTape.midBox ibox14),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox14 106 (FixedTape.rowsAux denominator ibox14 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox14) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_14
private noncomputable def tree13 : TapeTree := .split 1 (((1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree14 tree15
attribute [irreducible] tree13
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox13 1 (1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 : Int) false,decode_split denominator ibox13 1 (1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_14 h,accepted_15 h⟩
private noncomputable def tree12 : TapeTree := .split 2 (((1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree13 tree16
attribute [irreducible] tree12
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox12 2 (1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 : Int) false,decode_split denominator ibox12 2 (1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_13 h,accepted_16 h⟩
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
private noncomputable def tree9 : TapeTree := .split 2 (((1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree10 tree11
attribute [irreducible] tree9
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox9 2 (1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 : Int) false,decode_split denominator ibox9 2 (1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_10 h,accepted_11 h⟩
private noncomputable def tree8 : TapeTree := .split 1 (((1298394829376631939920388656638582251442519683014183739793921745588505317700357470959106103705600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree9 tree12
attribute [irreducible] tree8
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox8 1 (1298394829376631939920388656638582251442519683014183739793921745588505317700357470959106103705600000000000000000000000 : Int) false,decode_split denominator ibox8 1 (1298394829376631939920388656638582251442519683014183739793921745588505317700357470959106103705600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_9 h,accepted_12 h⟩
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
private noncomputable def tree4 : TapeTree := .split 1 (((1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree6
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 1 (1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 : Int) false,decode_split denominator ibox4 1 (1947592244064947909880582984957873377163779524521275609690882618382757976550536206438659155558400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_6 h⟩
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
private noncomputable def tree2 : TapeTree := .split 1 (((1298394829376631939920388656638582251442519683014183739793921745588505317700357470959106103705600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree4
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 1 (1298394829376631939920388656638582251442519683014183739793921745588505317700357470959106103705600000000000000000000000 : Int) false,decode_split denominator ibox2 1 (1298394829376631939920388656638582251442519683014183739793921745588505317700357470959106103705600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_4 h⟩
private noncomputable def tree1 : TapeTree := .split 2 (((1298394829376631939920388656638582251442519683014183739793921745588505317700357470959106103705600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree2 tree8
attribute [irreducible] tree1
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox1 2 (1298394829376631939920388656638582251442519683014183739793921745588505317700357470959106103705600000000000000000000000 : Int) false,decode_split denominator ibox1 2 (1298394829376631939920388656638582251442519683014183739793921745588505317700357470959106103705600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_2 h,accepted_8 h⟩
private noncomputable def tree0 : TapeTree := .face 3 false (candidateRows ibox0) tree1
attribute [irreducible] tree0
private theorem sign_0 : ((computed denominator ibox0).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox0,?_,accepted_1 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox0)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox0).gradient 3).hi) denominator_positive).1 sign_0
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (2708333333333333/10000000000000000 : ℚ) (9/32 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 106 = e113 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (2708333333333333/10000000000000000 : ℚ) (9/32 : ℚ)) x → eval e113 x ≤ 0 := by
  have hb := h.child_4 tape 106 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell44_high_internal_bottom

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell44_high_internal_bottom
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((2708333333333333/10000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((9/32 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 44 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 44 p)
    (hkb : ((9/32 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((2708333333333333/10000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : A ≤ bStar), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell44_high_internal_bottom.cell_bound h.child_8 h.child_9 (Cell44_high_internal_bottom.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell44_high_internal_bottom
