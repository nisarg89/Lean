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
namespace Cell79_high_first_top
private noncomputable def qValues : Fin 4 → ℚ := ![(520226124482061600534328216028526206/640623904783637288736741965164205715 : ℚ),(1475914651877269293399500000000000000/1153123028610547119726135537295570287 : ℚ),(8123526105450165312395361044984788229/2968754022352175117206237097611067180 : ℚ),(-255194674565106620298250000000000000/148437701117608755860311854880553359 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics21.e2 qValues
private noncomputable abbrev e10 : PolyExpr := SharedFiniteSemantics21.e10 qValues
private noncomputable abbrev e14 : PolyExpr := SharedFiniteSemantics21.e14 qValues
private noncomputable abbrev e41 : PolyExpr := SharedFiniteSemantics21.e41 qValues
private noncomputable abbrev e110 : PolyExpr := SharedFiniteSemantics21.e110 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics21.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics21.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics21.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics21.node_4 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics21.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics21.node_7 qValues
private noncomputable abbrev node_8 := SharedFiniteSemantics21.node_8 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics21.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics21.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics21.node_11 qValues
private noncomputable abbrev node_12 := SharedFiniteSemantics21.node_12 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics21.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics21.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics21.node_15 qValues
private noncomputable abbrev node_16 := SharedFiniteSemantics21.node_16 qValues
private noncomputable abbrev node_35 := SharedFiniteSemantics21.node_35 qValues
private noncomputable abbrev node_36 := SharedFiniteSemantics21.node_36 qValues
private noncomputable abbrev node_37 := SharedFiniteSemantics21.node_37 qValues
private noncomputable abbrev node_38 := SharedFiniteSemantics21.node_38 qValues
private noncomputable abbrev node_39 := SharedFiniteSemantics21.node_39 qValues
private noncomputable abbrev node_40 := SharedFiniteSemantics21.node_40 qValues
private noncomputable abbrev node_41 := SharedFiniteSemantics21.node_41 qValues
private noncomputable abbrev node_72 := SharedFiniteSemantics21.node_72 qValues
private noncomputable abbrev node_73 := SharedFiniteSemantics21.node_73 qValues
private noncomputable abbrev node_74 := SharedFiniteSemantics21.node_74 qValues
private noncomputable abbrev node_75 := SharedFiniteSemantics21.node_75 qValues
private noncomputable abbrev node_76 := SharedFiniteSemantics21.node_76 qValues
private noncomputable abbrev node_77 := SharedFiniteSemantics21.node_77 qValues
private noncomputable abbrev node_78 := SharedFiniteSemantics21.node_78 qValues
private noncomputable abbrev node_79 := SharedFiniteSemantics21.node_79 qValues
private noncomputable abbrev node_80 := SharedFiniteSemantics21.node_80 qValues
private noncomputable abbrev node_81 := SharedFiniteSemantics21.node_81 qValues
private noncomputable abbrev node_82 := SharedFiniteSemantics21.node_82 qValues
private noncomputable abbrev node_83 := SharedFiniteSemantics21.node_83 qValues
private noncomputable abbrev node_84 := SharedFiniteSemantics21.node_84 qValues
private noncomputable abbrev node_85 := SharedFiniteSemantics21.node_85 qValues
private noncomputable abbrev node_90 := SharedFiniteSemantics21.node_90 qValues
private noncomputable abbrev node_91 := SharedFiniteSemantics21.node_91 qValues
private noncomputable abbrev node_92 := SharedFiniteSemantics21.node_92 qValues
private noncomputable abbrev node_93 := SharedFiniteSemantics21.node_93 qValues
private noncomputable abbrev node_94 := SharedFiniteSemantics21.node_94 qValues
private noncomputable abbrev node_95 := SharedFiniteSemantics21.node_95 qValues
private noncomputable abbrev node_109 := SharedFiniteSemantics21.node_109 qValues
private noncomputable abbrev node_110 := SharedFiniteSemantics21.node_110 qValues
private noncomputable abbrev semantic_H_60 := SharedFiniteSemantics21.semantic_H_60 qValues
private noncomputable abbrev semantic_H_71 := SharedFiniteSemantics21.semantic_H_71 qValues
private noncomputable abbrev semantic_psi_34 := SharedFiniteSemantics21.semantic_psi_34 qValues
private noncomputable abbrev semantic_psi_108 := SharedFiniteSemantics21.semantic_psi_108 qValues
private noncomputable def aPoint (x : Fin 4 → ℝ) : ℝ := bStar+(x 0-bStar)*x 1
private noncomputable def rPoint (x : Fin 4 → ℝ) : ℝ := aPoint x+(1-aPoint x)*x 2
private noncomputable def yPoint (x : Fin 4 → ℝ) : ℝ := aPoint x+1-x 0
private theorem point_10 (x : Fin 4 → ℝ) : eval e10 x = aPoint x := by
  simp only [node_2,node_3,node_6,node_7,node_8,node_9,node_10] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_14 (x : Fin 4 → ℝ) : eval e14 x = rPoint x := by
  simp only [node_1,node_2,node_3,node_4,node_6,node_7,node_8,node_9,node_10,node_11,node_12,node_13,node_14] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_2 (x : Fin 4 → ℝ) : eval e2 x = x 0 := by
  simp only [node_2] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_41 (x : Fin 4 → ℝ) : eval e41 x = yPoint x := by
  simp only [node_1,node_2,node_3,node_6,node_7,node_8,node_9,node_10,node_39,node_40,node_41] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem price_lambda_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceLambda 79 p = ((520226124482061600534328216028526206/640623904783637288736741965164205715 : ℝ)+(1475914651877269293399500000000000000/1153123028610547119726135537295570287 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell79,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 79 p = (((8123526105450165312395361044984788229/2968754022352175117206237097611067180 : ℝ)+(-255194674565106620298250000000000000/148437701117608755860311854880553359 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell79,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e110 x = (x 0*(1-x 0))*(aPoint x+priceLambda 79 (x 0)*(HStar (yPoint x)-HStar (aPoint x))+priceTau 79 (x 0)*psiStar (rPoint x)+(cStar-aPoint x-eta (0 : Fin 9)*psiStar (aPoint x))-(cStar)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_11,node_15,node_16,node_35,node_36,node_37,node_38,node_39,node_40,node_72,node_73,node_74,node_75,node_76,node_77,node_78,node_79,node_80,node_81,node_82,node_83,node_84,node_85,node_90,node_91,node_92,node_93,node_94,node_95,node_109,node_110,semantic_H_60,semantic_H_71,semantic_psi_34,semantic_psi_108,point_10,point_14,point_2,point_41]
  norm_num [qValues,eta,etas,Fin.val_zero,sourceDenom,muStar,cStar] at *
  generalize HStar (yPoint x) = z0 at *
  generalize HStar (aPoint x) = z1 at *
  generalize psiStar (aPoint x) = z2 at *
  generalize psiStar (rPoint x) = z3 at *
  generalize sourceF0 (aPoint x) = z4 at *
  generalize sourceInc (aPoint x) (1-x 0) = z5 at *
  generalize sourceInc (aPoint x) ((1-x 0)*x 2) = z6 at *
  generalize sourcePD (aPoint x) (rPoint x) (rPoint x-aPoint x) = z7 at *
  field_simp [hp0,heps] <;> ring
theorem actual_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) (ha : bStar < aPoint x)
    (hL : lambdaStar (x 0) = priceLambda 79 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 79 (x 0)) :
    (1)*eval e110 x = (x 0*(1-x 0))*(firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_neg (not_le.mpr ha),hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (568037896359/1000000000000 : ℚ) (2864583333333333/5000000000000000 : ℚ)) x → eval e110 x ≤ 0)
    (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((568037896359/1000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((2864583333333333/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 79 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 79 p)
    (hkb : ((2864583333333333/5000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((568037896359/1000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : bStar < a) :
    firstResidual (0 : Fin 9) a p r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxr⟩ := h5 (568037896359/1000000000000 : ℚ) (2864583333333333/5000000000000000 : ℚ) bStar p a r hpcell hkb hr.2 hap hcase
  have hax : aPoint x = a := by simpa only [aPoint,rPoint] using hxa
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 79 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 79 (x 0) := by simpa only [hxp] using hT
  have hflag : bStar < aPoint x := by simpa only [hax] using hcase
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e110 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
  rw [actual_identity hs x hpx hflag hLx hTx] at hv
  have hscale : 0 < x 0*(1-x 0) := mul_pos hpx.1 (sub_pos.mpr hpx.2)
  have hv : firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x) ≤ 0 := le_of_not_gt (fun hpos => (not_lt_of_ge hv) (mul_pos hscale hpos))
  simpa only [hxp,hax,hrx] using hv
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
.neg 8,
.add 0 9,
.mul 10 3,
.add 8 11,
.const (113609/200000 : ℚ),
.add 13 9,
.const (1085/4818 : ℚ),
.const (19/73 : ℚ),
.mul 16 8,
.mul 8 8,
.const (35/146 : ℚ),
.mul 19 18,
.add 17 20,
.mul 18 18,
.mul 22 22,
.mul 23 23,
.mul 24 24,
.const (1/2 : ℚ),
.mul 26 25,
.add 21 27,
.neg 28,
.add 15 29,
.const (4818/3733 : ℚ),
.mul 31 30,
.const (145513/100000 : ℚ),
.mul 33 32,
.neg 34,
.add 14 35,
.neg 1,
.add 0 37,
.add 8 38,
.mul 15 39,
.mul 39 39,
.const (19/146 : ℚ),
.mul 42 41,
.mul 39 41,
.const (35/438 : ℚ),
.mul 45 44,
.add 43 46,
.mul 41 41,
.mul 48 48,
.mul 49 49,
.mul 50 50,
.mul 39 51,
.const (1/66 : ℚ),
.mul 53 52,
.add 47 54,
.neg 55,
.add 40 56,
.mul 31 57,
.mul 15 8,
.mul 42 18,
.mul 8 18,
.mul 45 61,
.add 60 62,
.mul 8 25,
.mul 53 64,
.add 63 65,
.neg 66,
.add 59 67,
.mul 31 68,
.neg 69,
.add 58 70,
.const (520226124482061600534328216028526206/640623904783637288736741965164205715 : ℚ),
.const (1475914651877269293399500000000000000/1153123028610547119726135537295570287 : ℚ),
.mul 73 1,
.add 72 74,
.const (8123526105450165312395361044984788229/2968754022352175117206237097611067180 : ℚ),
.const (-255194674565106620298250000000000000/148437701117608755860311854880553359 : ℚ),
.mul 77 1,
.add 76 78,
.mul 1 38,
.const (-145513/100000 : ℚ),
.add 79 81,
.mul 82 80,
.add 8 36,
.const (-113609/200000 : ℚ),
.add 84 85,
.mul 86 80,
.mul 75 71,
.add 87 88,
.mul 16 12,
.mul 12 12,
.mul 19 91,
.add 90 92,
.mul 91 91,
.mul 94 94,
.mul 95 95,
.mul 96 96,
.mul 26 97,
.add 93 98,
.neg 99,
.add 15 100,
.mul 31 101,
.mul 83 102,
.add 89 103]
private noncomputable def ssaQVals : Fin 19 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(-2840189/5000000 : ℚ),(113609/200000 : ℚ),(1085/4818 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ),(4818/3733 : ℚ),(145513/100000 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(520226124482061600534328216028526206/640623904783637288736741965164205715 : ℚ),(1475914651877269293399500000000000000/1153123028610547119726135537295570287 : ℚ),(8123526105450165312395361044984788229/2968754022352175117206237097611067180 : ℚ),(-255194674565106620298250000000000000/148437701117608755860311854880553359 : ℚ),(-145513/100000 : ℚ),(-113609/200000 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_e45357981b975f1d.p105 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_e45357981b975f1d.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 104 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_e45357981b975f1d.ssa_matches ssaQVals D B

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
private noncomputable def denominator : Int := 3424214851962772713501907003358878660397593051153714185170856725111163641420729638259471155200000000000000000000000
private theorem denominator_positive : 0 < denominator := by decide +kernel
private noncomputable def candidateRows (B : Fin 4 → FixedTape.I) : List TapeBounds :=
  (FixedTape.rowsAux denominator B [] tape).map (FixedTape.decodeRow denominator)
private theorem root_in_range : 104 < tape.length := by decide +kernel
private theorem references_valid : tapeRefsValidAux 0 tape = true := by decide +kernel
private theorem candidate_valid (h : Needs) (B : Fin 4 → FixedTape.I) :
    tapeCheck (FixedTape.decodeBox denominator B) tape (candidateRows B) = true :=
  h.child_10.1 denominator denominator_positive B tape references_valid
private theorem candidate_root (B : Fin 4 → FixedTape.I) :
    (candidateRows B).getD 104 zeroTapeBounds = FixedTape.decodeRow denominator (computed denominator B) := by
  unfold candidateRows
  rw [←decode_zeroRow denominator,List.getD_map,ssa_matches]
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨1945083801190178014358469450322826981377384719324312083693991247125933325299237461771793037207647603916800000000000,1961789758937004972162810756489509999058987461631571392081266588513991824840178014508579254618024116035256320000000⟩,⟨0,3424214851962772713501907003358878660397593051153714185170856725111163641420729638259471155200000000000000000000000⟩,⟨0,3424214851962772713501907003358878660397593051153714185170856725111163641420729638259471155200000000000000000000000⟩,⟨0,3424214851962772713501907003358878660397593051153714185170856725111163641420729638259471155200000000000000000000000⟩]
private noncomputable def tree0 : TapeTree := .direct (candidateRows ibox0)
attribute [irreducible] tree0
private theorem sign_0 : (computed denominator ibox0).value.hi ≤ 0 := by decide +kernel
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 104 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox0,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox0).value.hi denominator_positive).1 sign_0
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (568037896359/1000000000000 : ℚ) (2864583333333333/5000000000000000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 104 = e110 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (568037896359/1000000000000 : ℚ) (2864583333333333/5000000000000000 : ℚ)) x → eval e110 x ≤ 0 := by
  have hb := h.child_4 tape 104 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell79_high_first_top

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell79_high_first_top
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((568037896359/1000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((2864583333333333/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 79 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 79 p)
    (hkb : ((2864583333333333/5000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((568037896359/1000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : bStar < a), firstResidual (0 : Fin 9) a p r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell79_high_first_top.cell_bound h.child_8 h.child_9 (Cell79_high_first_top.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell79_high_first_top
