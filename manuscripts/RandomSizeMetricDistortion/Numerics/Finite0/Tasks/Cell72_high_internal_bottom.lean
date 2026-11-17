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
namespace Cell72_high_internal_bottom
private noncomputable def qValues : Fin 4 → ℚ := ![(366902146264616497729732138815969949/459459719138880938071217650032065763 : ℚ),(599241043180560786200000000000000000/459459719138880938071217650032065763 : ℚ),(118316999101778502527161218382177659650/44349499126141463252213457276151963683 : ℚ),(-70629856143068991134930000000000000000/44349499126141463252213457276151963683 : ℚ)]
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
    priceLambda 72 p = ((366902146264616497729732138815969949/459459719138880938071217650032065763 : ℝ)+(599241043180560786200000000000000000/459459719138880938071217650032065763 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell72,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 72 p = (((118316999101778502527161218382177659650/44349499126141463252213457276151963683 : ℝ)+(-70629856143068991134930000000000000000/44349499126141463252213457276151963683 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell72,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e113 x = (x 0*(1-x 0))*(aPoint x+priceLambda 72 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 72 (x 0)*psiStar (rPoint x)+(0)-(0)) := by
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
    (hL : lambdaStar (x 0) = priceLambda 72 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 72 (x 0)) :
    (1)*eval e113 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,if_pos hA,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (2604166666666667/5000000000000000 : ℚ) (17/32 : ℚ)) x → eval e113 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((2604166666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((17/32 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 72 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 72 p)
    (hkb : ((17/32 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((2604166666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : A ≤ bStar) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h6 (2604166666666667/5000000000000000 : ℚ) (17/32 : ℚ) bStar p a A r hpcell hkb hr ha hap hpA hcase
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 72 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 72 (x 0) := by simpa only [hxp] using hT
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
.const (366902146264616497729732138815969949/459459719138880938071217650032065763 : ℚ),
.const (599241043180560786200000000000000000/459459719138880938071217650032065763 : ℚ),
.mul 74 1,
.add 73 75,
.const (118316999101778502527161218382177659650/44349499126141463252213457276151963683 : ℚ),
.const (-70629856143068991134930000000000000000/44349499126141463252213457276151963683 : ℚ),
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
private noncomputable def ssaQVals : Fin 16 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(2159811/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(366902146264616497729732138815969949/459459719138880938071217650032065763 : ℚ),(599241043180560786200000000000000000/459459719138880938071217650032065763 : ℚ),(118316999101778502527161218382177659650/44349499126141463252213457276151963683 : ℚ),(-70629856143068991134930000000000000000/44349499126141463252213457276151963683 : ℚ),(-145513/100000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
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
private noncomputable def denominator : Int := 2534072753371217012736408162813206114744496805015787292124524357151593124358852154787410581913600000000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨1319829559047509029738396142879679033856636273492796864281310103735607560571859307391317968670143652494038794240000000,1346226150228459038016216836494515748458013927664636998941153564736783847315640207230811871641600000000000000000000000⟩,⟨0,2534072753371217012736408162813206114744496805015787292124524357151593124358852154787410581913600000000000000000000000⟩,⟨0,2534072753371217012736408162813206114744496805015787292124524357151593124358852154787410581913600000000000000000000000⟩,⟨0,2534072753371217012736408162813206114744496805015787292124524357151593124358852154787410581913600000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 3 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := splitI ibox1 1 1267036376685608506368204081406603057372248402507893646062262178575796562179426077393705290956800000000000000000000000 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox1 1 1267036376685608506368204081406603057372248402507893646062262178575796562179426077393705290956800000000000000000000000 true
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 1900554565028412759552306122109904586058372603761840469093393267863694843269139116090557936435200000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox3 1 1900554565028412759552306122109904586058372603761840469093393267863694843269139116090557936435200000000000000000000000 true
private noncomputable def ibox6 : Fin 4 → FixedTape.I := faceI ibox5 1 true
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 2 1267036376685608506368204081406603057372248402507893646062262178575796562179426077393705290956800000000000000000000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox7 0 1333027854637984033877306489687097391157325100578716931611231834236195703943749757311064920155871826247019397120000000 false
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox7 0 1333027854637984033877306489687097391157325100578716931611231834236195703943749757311064920155871826247019397120000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox6 2 1267036376685608506368204081406603057372248402507893646062262178575796562179426077393705290956800000000000000000000000 true
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox10 0 1333027854637984033877306489687097391157325100578716931611231834236195703943749757311064920155871826247019397120000000 false
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox10 0 1333027854637984033877306489687097391157325100578716931611231834236195703943749757311064920155871826247019397120000000 true
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
private noncomputable def tree10 : TapeTree := .split 0 (((1333027854637984033877306489687097391157325100578716931611231834236195703943749757311064920155871826247019397120000000 : Int) : ℚ)/(denominator : ℚ)) tree11 tree12
attribute [irreducible] tree10
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox10 0 (1333027854637984033877306489687097391157325100578716931611231834236195703943749757311064920155871826247019397120000000 : Int) false,decode_split denominator ibox10 0 (1333027854637984033877306489687097391157325100578716931611231834236195703943749757311064920155871826247019397120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_11 h,accepted_12 h⟩
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
private noncomputable def tree7 : TapeTree := .split 0 (((1333027854637984033877306489687097391157325100578716931611231834236195703943749757311064920155871826247019397120000000 : Int) : ℚ)/(denominator : ℚ)) tree8 tree9
attribute [irreducible] tree7
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox7 0 (1333027854637984033877306489687097391157325100578716931611231834236195703943749757311064920155871826247019397120000000 : Int) false,decode_split denominator ibox7 0 (1333027854637984033877306489687097391157325100578716931611231834236195703943749757311064920155871826247019397120000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_8 h,accepted_9 h⟩
private noncomputable def tree6 : TapeTree := .split 2 (((1267036376685608506368204081406603057372248402507893646062262178575796562179426077393705290956800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree10
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 2 (1267036376685608506368204081406603057372248402507893646062262178575796562179426077393705290956800000000000000000000000 : Int) false,decode_split denominator ibox6 2 (1267036376685608506368204081406603057372248402507893646062262178575796562179426077393705290956800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_7 h,accepted_10 h⟩
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
private noncomputable def tree3 : TapeTree := .split 1 (((1900554565028412759552306122109904586058372603761840469093393267863694843269139116090557936435200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree5
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (1900554565028412759552306122109904586058372603761840469093393267863694843269139116090557936435200000000000000000000000 : Int) false,decode_split denominator ibox3 1 (1900554565028412759552306122109904586058372603761840469093393267863694843269139116090557936435200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_5 h⟩
private noncomputable def tree2 : TapeTree := .centered (candidateRows ibox2) (candidateRows (FixedTape.midBox ibox2))
attribute [irreducible] tree2
private theorem sign_2 : 2*denominator*(computed denominator (FixedTape.midBox ibox2)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox2).gradient k).lo.natAbs ((computed denominator ibox2).gradient k).hi.natAbs : Int)*((ibox2 k).hi-(ibox2 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox2
    (computed denominator ibox2) (computed denominator (FixedTape.midBox ibox2))
    (by decide +kernel)
private theorem midpoint_even_2 : ∀ k, 2 ∣ (ibox2 k).lo+(ibox2 k).hi := by decide +kernel
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox2 midpoint_even_2
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox2,candidate_valid h (FixedTape.midBox ibox2),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox2 106 (FixedTape.rowsAux denominator ibox2 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox2) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_2
private noncomputable def tree1 : TapeTree := .split 1 (((1267036376685608506368204081406603057372248402507893646062262178575796562179426077393705290956800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree2 tree3
attribute [irreducible] tree1
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox1 1 (1267036376685608506368204081406603057372248402507893646062262178575796562179426077393705290956800000000000000000000000 : Int) false,decode_split denominator ibox1 1 (1267036376685608506368204081406603057372248402507893646062262178575796562179426077393705290956800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_2 h,accepted_3 h⟩
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
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (2604166666666667/5000000000000000 : ℚ) (17/32 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 106 = e113 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (2604166666666667/5000000000000000 : ℚ) (17/32 : ℚ)) x → eval e113 x ≤ 0 := by
  have hb := h.child_4 tape 106 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell72_high_internal_bottom

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell72_high_internal_bottom
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((2604166666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((17/32 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 72 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 72 p)
    (hkb : ((17/32 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((2604166666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : A ≤ bStar), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell72_high_internal_bottom.cell_bound h.child_8 h.child_9 (Cell72_high_internal_bottom.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell72_high_internal_bottom
