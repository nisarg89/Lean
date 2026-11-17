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
namespace Cell119_high_first_top
private noncomputable def qValues : Fin 2 → ℚ := ![(9103267648564165688987073613400768701/1421551611385732114735867686811794492 : ℚ),(-5575573568591213016781250000000000000/1066163708539299086051900765108845869 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics26.e2 qValues
private noncomputable abbrev e10 : PolyExpr := SharedFiniteSemantics26.e10 qValues
private noncomputable abbrev e14 : PolyExpr := SharedFiniteSemantics26.e14 qValues
private noncomputable abbrev e41 : PolyExpr := SharedFiniteSemantics26.e41 qValues
private noncomputable abbrev e89 : PolyExpr := SharedFiniteSemantics26.e89 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics26.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics26.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics26.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics26.node_4 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics26.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics26.node_7 qValues
private noncomputable abbrev node_8 := SharedFiniteSemantics26.node_8 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics26.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics26.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics26.node_11 qValues
private noncomputable abbrev node_12 := SharedFiniteSemantics26.node_12 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics26.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics26.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics26.node_15 qValues
private noncomputable abbrev node_16 := SharedFiniteSemantics26.node_16 qValues
private noncomputable abbrev node_35 := SharedFiniteSemantics26.node_35 qValues
private noncomputable abbrev node_36 := SharedFiniteSemantics26.node_36 qValues
private noncomputable abbrev node_37 := SharedFiniteSemantics26.node_37 qValues
private noncomputable abbrev node_38 := SharedFiniteSemantics26.node_38 qValues
private noncomputable abbrev node_39 := SharedFiniteSemantics26.node_39 qValues
private noncomputable abbrev node_40 := SharedFiniteSemantics26.node_40 qValues
private noncomputable abbrev node_41 := SharedFiniteSemantics26.node_41 qValues
private noncomputable abbrev node_72 := SharedFiniteSemantics26.node_72 qValues
private noncomputable abbrev node_73 := SharedFiniteSemantics26.node_73 qValues
private noncomputable abbrev node_74 := SharedFiniteSemantics26.node_74 qValues
private noncomputable abbrev node_75 := SharedFiniteSemantics26.node_75 qValues
private noncomputable abbrev node_76 := SharedFiniteSemantics26.node_76 qValues
private noncomputable abbrev node_77 := SharedFiniteSemantics26.node_77 qValues
private noncomputable abbrev node_78 := SharedFiniteSemantics26.node_78 qValues
private noncomputable abbrev node_84 := SharedFiniteSemantics26.node_84 qValues
private noncomputable abbrev node_85 := SharedFiniteSemantics26.node_85 qValues
private noncomputable abbrev node_86 := SharedFiniteSemantics26.node_86 qValues
private noncomputable abbrev node_87 := SharedFiniteSemantics26.node_87 qValues
private noncomputable abbrev node_88 := SharedFiniteSemantics26.node_88 qValues
private noncomputable abbrev node_89 := SharedFiniteSemantics26.node_89 qValues
private noncomputable abbrev semantic_H_60 := SharedFiniteSemantics26.semantic_H_60 qValues
private noncomputable abbrev semantic_H_71 := SharedFiniteSemantics26.semantic_H_71 qValues
private noncomputable abbrev semantic_psi_34 := SharedFiniteSemantics26.semantic_psi_34 qValues
private noncomputable abbrev semantic_psi_102 := SharedFiniteSemantics26.semantic_psi_102 qValues
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
    priceLambda 119 p = ((9103267648564165688987073613400768701/1421551611385732114735867686811794492 : ℝ)+(-5575573568591213016781250000000000000/1066163708539299086051900765108845869 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell119,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 119 p = 0 := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell119,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e89 x = (x 0*(1-x 0))*(aPoint x+priceLambda 119 (x 0)*(HStar (yPoint x)-HStar (aPoint x))+priceTau 119 (x 0)*psiStar (rPoint x)+(cStar-aPoint x-eta (0 : Fin 9)*psiStar (aPoint x))-(cStar)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_11,node_15,node_16,node_35,node_36,node_37,node_38,node_39,node_40,node_72,node_73,node_74,node_75,node_76,node_77,node_78,node_84,node_85,node_86,node_87,node_88,node_89,semantic_H_60,semantic_H_71,semantic_psi_34,semantic_psi_102,point_10,point_14,point_2,point_41]
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
    (hL : lambdaStar (x 0) = priceLambda 119 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 119 (x 0)) :
    (1)*eval e89 x = (x 0*(1-x 0))*(firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_neg (not_le.mpr ha),hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (4635416666666667/5000000000000000 : ℚ) (15/16 : ℚ)) x → eval e89 x ≤ 0)
    (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((4635416666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((15/16 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 119 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 119 p)
    (hkb : ((15/16 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((4635416666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : bStar < a) :
    firstResidual (0 : Fin 9) a p r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxr⟩ := h5 (4635416666666667/5000000000000000 : ℚ) (15/16 : ℚ) bStar p a r hpcell hkb hr.2 hap hcase
  have hax : aPoint x = a := by simpa only [aPoint,rPoint] using hxa
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 119 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 119 (x 0) := by simpa only [hxp] using hT
  have hflag : bStar < aPoint x := by simpa only [hax] using hcase
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e89 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
  rw [actual_identity hs x hpx hflag hLx hTx] at hv
  have hscale : 0 < x 0*(1-x 0) := mul_pos hpx.1 (sub_pos.mpr hpx.2)
  have hv : firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x) ≤ 0 := le_of_not_gt (fun hpos => (not_lt_of_ge hv) (mul_pos hscale hpos))
  simpa only [hxp,hax,hrx] using hv
private noncomputable def tape : List TapeOp := [
.const (1/1 : ℚ),
.var 0,
.var 1,
.const (2840189/5000000 : ℚ),
.const (-2840189/5000000 : ℚ),
.add 1 4,
.mul 5 2,
.add 3 6,
.neg 7,
.const (113609/200000 : ℚ),
.add 9 8,
.const (1085/4818 : ℚ),
.const (19/73 : ℚ),
.mul 12 7,
.mul 7 7,
.const (35/146 : ℚ),
.mul 15 14,
.add 13 16,
.mul 14 14,
.mul 18 18,
.mul 19 19,
.mul 20 20,
.const (1/2 : ℚ),
.mul 22 21,
.add 17 23,
.neg 24,
.add 11 25,
.const (4818/3733 : ℚ),
.mul 27 26,
.const (145513/100000 : ℚ),
.mul 29 28,
.neg 30,
.add 10 31,
.neg 1,
.add 0 33,
.add 7 34,
.mul 11 35,
.mul 35 35,
.const (19/146 : ℚ),
.mul 38 37,
.mul 35 37,
.const (35/438 : ℚ),
.mul 41 40,
.add 39 42,
.mul 37 37,
.mul 44 44,
.mul 45 45,
.mul 46 46,
.mul 35 47,
.const (1/66 : ℚ),
.mul 49 48,
.add 43 50,
.neg 51,
.add 36 52,
.mul 27 53,
.mul 11 7,
.mul 38 14,
.mul 7 14,
.mul 41 57,
.add 56 58,
.mul 7 21,
.mul 49 60,
.add 59 61,
.neg 62,
.add 55 63,
.mul 27 64,
.neg 65,
.add 54 66,
.const (9103267648564165688987073613400768701/1421551611385732114735867686811794492 : ℚ),
.const (-5575573568591213016781250000000000000/1066163708539299086051900765108845869 : ℚ),
.mul 69 1,
.add 68 70,
.mul 1 34,
.add 7 32,
.const (-113609/200000 : ℚ),
.add 73 74,
.mul 75 72,
.mul 71 67,
.add 76 77]
private noncomputable def ssaQVals : Fin 16 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(-2840189/5000000 : ℚ),(113609/200000 : ℚ),(1085/4818 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ),(4818/3733 : ℚ),(145513/100000 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(9103267648564165688987073613400768701/1421551611385732114735867686811794492 : ℚ),(-5575573568591213016781250000000000000/1066163708539299086051900765108845869 : ℚ),(-113609/200000 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_78ba41088e0f0938.p79 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_78ba41088e0f0938.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 78 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_78ba41088e0f0938.ssa_matches ssaQVals D B

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
private noncomputable def denominator : Int := 25320776177093475749362122887307928612340100290292596691192754650847641600000000000000000000000
private theorem denominator_positive : 0 < denominator := by decide +kernel
private noncomputable def candidateRows (B : Fin 4 → FixedTape.I) : List TapeBounds :=
  (FixedTape.rowsAux denominator B [] tape).map (FixedTape.decodeRow denominator)
private theorem root_in_range : 78 < tape.length := by decide +kernel
private theorem references_valid : tapeRefsValidAux 0 tape = true := by decide +kernel
private theorem candidate_valid (h : Needs) (B : Fin 4 → FixedTape.I) :
    tapeCheck (FixedTape.decodeBox denominator B) tape (candidateRows B) = true :=
  h.child_10.1 denominator denominator_positive B tape references_valid
private theorem candidate_root (B : Fin 4 → FixedTape.I) :
    (candidateRows B).getD 78 zeroTapeBounds = FixedTape.decodeRow denominator (computed denominator B) := by
  unfold candidateRows
  rw [←decode_zeroRow denominator,List.getD_map,ssa_matches]
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨23474469580847078164022879899673442108498493797987335671799968977063113812850310056509440000000,23738227666025133515026990206851183074068844022149309397993207485169664000000000000000000000000⟩,⟨0,25320776177093475749362122887307928612340100290292596691192754650847641600000000000000000000000⟩,⟨0,25320776177093475749362122887307928612340100290292596691192754650847641600000000000000000000000⟩,⟨0,25320776177093475749362122887307928612340100290292596691192754650847641600000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 2 true
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 3 true
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 1 12660388088546737874681061443653964306170050145146298345596377325423820800000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 6330194044273368937340530721826982153085025072573149172798188662711910400000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 1 3165097022136684468670265360913491076542512536286574586399094331355955200000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox5 0 23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 false
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 1 1582548511068342234335132680456745538271256268143287293199547165677977600000000000000000000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox6 1 1582548511068342234335132680456745538271256268143287293199547165677977600000000000000000000000 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox5 0 23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox9 1 1582548511068342234335132680456745538271256268143287293199547165677977600000000000000000000000 false
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox9 1 1582548511068342234335132680456745538271256268143287293199547165677977600000000000000000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox4 1 3165097022136684468670265360913491076542512536286574586399094331355955200000000000000000000000 true
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox12 0 23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 false
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox12 0 23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 true
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox14 1 4747645533205026703005398041370236614813768804429861879598641497033932800000000000000000000000 false
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox14 1 4747645533205026703005398041370236614813768804429861879598641497033932800000000000000000000000 true
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox3 1 6330194044273368937340530721826982153085025072573149172798188662711910400000000000000000000000 true
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox17 1 9495291066410053406010796082740473229627537608859723759197282994067865600000000000000000000000 false
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox18 0 23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 false
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox18 0 23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 true
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox20 1 7912742555341711171675663402283727691356281340716436465997735828389888000000000000000000000000 false
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox20 1 7912742555341711171675663402283727691356281340716436465997735828389888000000000000000000000000 true
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox17 1 9495291066410053406010796082740473229627537608859723759197282994067865600000000000000000000000 true
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox23 0 23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 false
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox23 0 23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 true
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox25 1 11077839577478395640345928763197218767898793877003011052396830159745843200000000000000000000000 false
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox25 1 11077839577478395640345928763197218767898793877003011052396830159745843200000000000000000000000 true
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox2 1 12660388088546737874681061443653964306170050145146298345596377325423820800000000000000000000000 true
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox28 1 18990582132820106812021592165480946459255075217719447518394565988135731200000000000000000000000 false
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox29 1 15825485110683422343351326804567455382712562681432872931995471656779776000000000000000000000000 false
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox30 0 23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 false
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox30 0 23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 true
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox29 1 15825485110683422343351326804567455382712562681432872931995471656779776000000000000000000000000 true
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox33 1 17408033621751764577686459485024200920983818949576160225195018822457753600000000000000000000000 false
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox33 1 17408033621751764577686459485024200920983818949576160225195018822457753600000000000000000000000 true
private noncomputable def ibox36 : Fin 4 → FixedTape.I := splitI ibox28 1 18990582132820106812021592165480946459255075217719447518394565988135731200000000000000000000000 true
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox36 1 22155679154956791280691857526394437535797587754006022104793660319491686400000000000000000000000 false
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox37 1 20573130643888449046356724845937691997526331485862734811594113153813708800000000000000000000000 false
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox37 1 20573130643888449046356724845937691997526331485862734811594113153813708800000000000000000000000 true
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox36 1 22155679154956791280691857526394437535797587754006022104793660319491686400000000000000000000000 true
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox40 1 23738227666025133515026990206851183074068844022149309397993207485169664000000000000000000000000 false
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox41 1 22946953410490962397859423866622810304933215888077665751393433902330675200000000000000000000000 false
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox41 1 22946953410490962397859423866622810304933215888077665751393433902330675200000000000000000000000 true
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox40 1 23738227666025133515026990206851183074068844022149309397993207485169664000000000000000000000000 true
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox44 1 24529501921559304632194556547079555843204472156220953044592981068008652800000000000000000000000 false
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox44 1 24529501921559304632194556547079555843204472156220953044592981068008652800000000000000000000000 true
private noncomputable def tree46 : TapeTree := .centered (candidateRows ibox46) (candidateRows (FixedTape.midBox ibox46))
attribute [irreducible] tree46
private theorem sign_46 : 2*denominator*(computed denominator (FixedTape.midBox ibox46)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox46).gradient k).lo.natAbs ((computed denominator ibox46).gradient k).hi.natAbs : Int)*((ibox46 k).hi-(ibox46 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox46
    (computed denominator ibox46) (computed denominator (FixedTape.midBox ibox46))
    (by decide +kernel)
private theorem midpoint_even_46 : ∀ k, 2 ∣ (ibox46 k).lo+(ibox46 k).hi := by decide +kernel
private theorem accepted_46 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox46) tree46 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox46 midpoint_even_46
  simp only [tree46,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox46,candidate_valid h (FixedTape.midBox ibox46),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox46 78 (FixedTape.rowsAux denominator ibox46 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox46) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_46
private noncomputable def tree45 : TapeTree := .centered (candidateRows ibox45) (candidateRows (FixedTape.midBox ibox45))
attribute [irreducible] tree45
private theorem sign_45 : 2*denominator*(computed denominator (FixedTape.midBox ibox45)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox45).gradient k).lo.natAbs ((computed denominator ibox45).gradient k).hi.natAbs : Int)*((ibox45 k).hi-(ibox45 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox45
    (computed denominator ibox45) (computed denominator (FixedTape.midBox ibox45))
    (by decide +kernel)
private theorem midpoint_even_45 : ∀ k, 2 ∣ (ibox45 k).lo+(ibox45 k).hi := by decide +kernel
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox45 midpoint_even_45
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox45,candidate_valid h (FixedTape.midBox ibox45),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox45 78 (FixedTape.rowsAux denominator ibox45 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox45) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_45
private noncomputable def tree44 : TapeTree := .split 1 (((24529501921559304632194556547079555843204472156220953044592981068008652800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree45 tree46
attribute [irreducible] tree44
private theorem accepted_44 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox44) tree44 = true := by
  simp only [tree44,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox44 1 (24529501921559304632194556547079555843204472156220953044592981068008652800000000000000000000000 : Int) false,decode_split denominator ibox44 1 (24529501921559304632194556547079555843204472156220953044592981068008652800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_45 h,accepted_46 h⟩
private noncomputable def tree43 : TapeTree := .centered (candidateRows ibox43) (candidateRows (FixedTape.midBox ibox43))
attribute [irreducible] tree43
private theorem sign_43 : 2*denominator*(computed denominator (FixedTape.midBox ibox43)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox43).gradient k).lo.natAbs ((computed denominator ibox43).gradient k).hi.natAbs : Int)*((ibox43 k).hi-(ibox43 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox43
    (computed denominator ibox43) (computed denominator (FixedTape.midBox ibox43))
    (by decide +kernel)
private theorem midpoint_even_43 : ∀ k, 2 ∣ (ibox43 k).lo+(ibox43 k).hi := by decide +kernel
private theorem accepted_43 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox43) tree43 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox43 midpoint_even_43
  simp only [tree43,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox43,candidate_valid h (FixedTape.midBox ibox43),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox43 78 (FixedTape.rowsAux denominator ibox43 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox43) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_43
private noncomputable def tree42 : TapeTree := .centered (candidateRows ibox42) (candidateRows (FixedTape.midBox ibox42))
attribute [irreducible] tree42
private theorem sign_42 : 2*denominator*(computed denominator (FixedTape.midBox ibox42)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox42).gradient k).lo.natAbs ((computed denominator ibox42).gradient k).hi.natAbs : Int)*((ibox42 k).hi-(ibox42 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox42
    (computed denominator ibox42) (computed denominator (FixedTape.midBox ibox42))
    (by decide +kernel)
private theorem midpoint_even_42 : ∀ k, 2 ∣ (ibox42 k).lo+(ibox42 k).hi := by decide +kernel
private theorem accepted_42 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox42) tree42 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox42 midpoint_even_42
  simp only [tree42,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox42,candidate_valid h (FixedTape.midBox ibox42),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox42 78 (FixedTape.rowsAux denominator ibox42 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox42) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_42
private noncomputable def tree41 : TapeTree := .split 1 (((22946953410490962397859423866622810304933215888077665751393433902330675200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree42 tree43
attribute [irreducible] tree41
private theorem accepted_41 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox41) tree41 = true := by
  simp only [tree41,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox41 1 (22946953410490962397859423866622810304933215888077665751393433902330675200000000000000000000000 : Int) false,decode_split denominator ibox41 1 (22946953410490962397859423866622810304933215888077665751393433902330675200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_42 h,accepted_43 h⟩
private noncomputable def tree40 : TapeTree := .split 1 (((23738227666025133515026990206851183074068844022149309397993207485169664000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree41 tree44
attribute [irreducible] tree40
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox40 1 (23738227666025133515026990206851183074068844022149309397993207485169664000000000000000000000000 : Int) false,decode_split denominator ibox40 1 (23738227666025133515026990206851183074068844022149309397993207485169664000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_41 h,accepted_44 h⟩
private noncomputable def tree39 : TapeTree := .centered (candidateRows ibox39) (candidateRows (FixedTape.midBox ibox39))
attribute [irreducible] tree39
private theorem sign_39 : 2*denominator*(computed denominator (FixedTape.midBox ibox39)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox39).gradient k).lo.natAbs ((computed denominator ibox39).gradient k).hi.natAbs : Int)*((ibox39 k).hi-(ibox39 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox39
    (computed denominator ibox39) (computed denominator (FixedTape.midBox ibox39))
    (by decide +kernel)
private theorem midpoint_even_39 : ∀ k, 2 ∣ (ibox39 k).lo+(ibox39 k).hi := by decide +kernel
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox39 midpoint_even_39
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox39,candidate_valid h (FixedTape.midBox ibox39),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox39 78 (FixedTape.rowsAux denominator ibox39 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox39) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_39
private noncomputable def tree38 : TapeTree := .centered (candidateRows ibox38) (candidateRows (FixedTape.midBox ibox38))
attribute [irreducible] tree38
private theorem sign_38 : 2*denominator*(computed denominator (FixedTape.midBox ibox38)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox38).gradient k).lo.natAbs ((computed denominator ibox38).gradient k).hi.natAbs : Int)*((ibox38 k).hi-(ibox38 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox38
    (computed denominator ibox38) (computed denominator (FixedTape.midBox ibox38))
    (by decide +kernel)
private theorem midpoint_even_38 : ∀ k, 2 ∣ (ibox38 k).lo+(ibox38 k).hi := by decide +kernel
private theorem accepted_38 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox38) tree38 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox38 midpoint_even_38
  simp only [tree38,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox38,candidate_valid h (FixedTape.midBox ibox38),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox38 78 (FixedTape.rowsAux denominator ibox38 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox38) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_38
private noncomputable def tree37 : TapeTree := .split 1 (((20573130643888449046356724845937691997526331485862734811594113153813708800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree38 tree39
attribute [irreducible] tree37
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox37 1 (20573130643888449046356724845937691997526331485862734811594113153813708800000000000000000000000 : Int) false,decode_split denominator ibox37 1 (20573130643888449046356724845937691997526331485862734811594113153813708800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_38 h,accepted_39 h⟩
private noncomputable def tree36 : TapeTree := .split 1 (((22155679154956791280691857526394437535797587754006022104793660319491686400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree37 tree40
attribute [irreducible] tree36
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox36 1 (22155679154956791280691857526394437535797587754006022104793660319491686400000000000000000000000 : Int) false,decode_split denominator ibox36 1 (22155679154956791280691857526394437535797587754006022104793660319491686400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_37 h,accepted_40 h⟩
private noncomputable def tree35 : TapeTree := .centered (candidateRows ibox35) (candidateRows (FixedTape.midBox ibox35))
attribute [irreducible] tree35
private theorem sign_35 : 2*denominator*(computed denominator (FixedTape.midBox ibox35)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox35).gradient k).lo.natAbs ((computed denominator ibox35).gradient k).hi.natAbs : Int)*((ibox35 k).hi-(ibox35 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox35
    (computed denominator ibox35) (computed denominator (FixedTape.midBox ibox35))
    (by decide +kernel)
private theorem midpoint_even_35 : ∀ k, 2 ∣ (ibox35 k).lo+(ibox35 k).hi := by decide +kernel
private theorem accepted_35 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox35) tree35 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox35 midpoint_even_35
  simp only [tree35,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox35,candidate_valid h (FixedTape.midBox ibox35),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox35 78 (FixedTape.rowsAux denominator ibox35 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox35) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_35
private noncomputable def tree34 : TapeTree := .centered (candidateRows ibox34) (candidateRows (FixedTape.midBox ibox34))
attribute [irreducible] tree34
private theorem sign_34 : 2*denominator*(computed denominator (FixedTape.midBox ibox34)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox34).gradient k).lo.natAbs ((computed denominator ibox34).gradient k).hi.natAbs : Int)*((ibox34 k).hi-(ibox34 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox34
    (computed denominator ibox34) (computed denominator (FixedTape.midBox ibox34))
    (by decide +kernel)
private theorem midpoint_even_34 : ∀ k, 2 ∣ (ibox34 k).lo+(ibox34 k).hi := by decide +kernel
private theorem accepted_34 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox34) tree34 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox34 midpoint_even_34
  simp only [tree34,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox34,candidate_valid h (FixedTape.midBox ibox34),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox34 78 (FixedTape.rowsAux denominator ibox34 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox34) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_34
private noncomputable def tree33 : TapeTree := .split 1 (((17408033621751764577686459485024200920983818949576160225195018822457753600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree34 tree35
attribute [irreducible] tree33
private theorem accepted_33 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox33) tree33 = true := by
  simp only [tree33,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox33 1 (17408033621751764577686459485024200920983818949576160225195018822457753600000000000000000000000 : Int) false,decode_split denominator ibox33 1 (17408033621751764577686459485024200920983818949576160225195018822457753600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_34 h,accepted_35 h⟩
private noncomputable def tree32 : TapeTree := .centered (candidateRows ibox32) (candidateRows (FixedTape.midBox ibox32))
attribute [irreducible] tree32
private theorem sign_32 : 2*denominator*(computed denominator (FixedTape.midBox ibox32)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox32).gradient k).lo.natAbs ((computed denominator ibox32).gradient k).hi.natAbs : Int)*((ibox32 k).hi-(ibox32 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox32
    (computed denominator ibox32) (computed denominator (FixedTape.midBox ibox32))
    (by decide +kernel)
private theorem midpoint_even_32 : ∀ k, 2 ∣ (ibox32 k).lo+(ibox32 k).hi := by decide +kernel
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox32 midpoint_even_32
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox32,candidate_valid h (FixedTape.midBox ibox32),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox32 78 (FixedTape.rowsAux denominator ibox32 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox32) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_32
private noncomputable def tree31 : TapeTree := .centered (candidateRows ibox31) (candidateRows (FixedTape.midBox ibox31))
attribute [irreducible] tree31
private theorem sign_31 : 2*denominator*(computed denominator (FixedTape.midBox ibox31)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox31).gradient k).lo.natAbs ((computed denominator ibox31).gradient k).hi.natAbs : Int)*((ibox31 k).hi-(ibox31 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox31
    (computed denominator ibox31) (computed denominator (FixedTape.midBox ibox31))
    (by decide +kernel)
private theorem midpoint_even_31 : ∀ k, 2 ∣ (ibox31 k).lo+(ibox31 k).hi := by decide +kernel
private theorem accepted_31 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox31) tree31 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox31 midpoint_even_31
  simp only [tree31,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox31,candidate_valid h (FixedTape.midBox ibox31),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox31 78 (FixedTape.rowsAux denominator ibox31 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox31) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_31
private noncomputable def tree30 : TapeTree := .split 0 (((23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 : Int) : ℚ)/(denominator : ℚ)) tree31 tree32
attribute [irreducible] tree30
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox30 0 (23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 : Int) false,decode_split denominator ibox30 0 (23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_31 h,accepted_32 h⟩
private noncomputable def tree29 : TapeTree := .split 1 (((15825485110683422343351326804567455382712562681432872931995471656779776000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree30 tree33
attribute [irreducible] tree29
private theorem accepted_29 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox29) tree29 = true := by
  simp only [tree29,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox29 1 (15825485110683422343351326804567455382712562681432872931995471656779776000000000000000000000000 : Int) false,decode_split denominator ibox29 1 (15825485110683422343351326804567455382712562681432872931995471656779776000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_30 h,accepted_33 h⟩
private noncomputable def tree28 : TapeTree := .split 1 (((18990582132820106812021592165480946459255075217719447518394565988135731200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree29 tree36
attribute [irreducible] tree28
private theorem accepted_28 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox28) tree28 = true := by
  simp only [tree28,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox28 1 (18990582132820106812021592165480946459255075217719447518394565988135731200000000000000000000000 : Int) false,decode_split denominator ibox28 1 (18990582132820106812021592165480946459255075217719447518394565988135731200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_29 h,accepted_36 h⟩
private noncomputable def tree27 : TapeTree := .centered (candidateRows ibox27) (candidateRows (FixedTape.midBox ibox27))
attribute [irreducible] tree27
private theorem sign_27 : 2*denominator*(computed denominator (FixedTape.midBox ibox27)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox27).gradient k).lo.natAbs ((computed denominator ibox27).gradient k).hi.natAbs : Int)*((ibox27 k).hi-(ibox27 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox27
    (computed denominator ibox27) (computed denominator (FixedTape.midBox ibox27))
    (by decide +kernel)
private theorem midpoint_even_27 : ∀ k, 2 ∣ (ibox27 k).lo+(ibox27 k).hi := by decide +kernel
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox27 midpoint_even_27
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox27,candidate_valid h (FixedTape.midBox ibox27),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox27 78 (FixedTape.rowsAux denominator ibox27 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox27) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_27
private noncomputable def tree26 : TapeTree := .centered (candidateRows ibox26) (candidateRows (FixedTape.midBox ibox26))
attribute [irreducible] tree26
private theorem sign_26 : 2*denominator*(computed denominator (FixedTape.midBox ibox26)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox26).gradient k).lo.natAbs ((computed denominator ibox26).gradient k).hi.natAbs : Int)*((ibox26 k).hi-(ibox26 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox26
    (computed denominator ibox26) (computed denominator (FixedTape.midBox ibox26))
    (by decide +kernel)
private theorem midpoint_even_26 : ∀ k, 2 ∣ (ibox26 k).lo+(ibox26 k).hi := by decide +kernel
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox26 midpoint_even_26
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox26,candidate_valid h (FixedTape.midBox ibox26),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox26 78 (FixedTape.rowsAux denominator ibox26 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox26) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_26
private noncomputable def tree25 : TapeTree := .split 1 (((11077839577478395640345928763197218767898793877003011052396830159745843200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree26 tree27
attribute [irreducible] tree25
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox25 1 (11077839577478395640345928763197218767898793877003011052396830159745843200000000000000000000000 : Int) false,decode_split denominator ibox25 1 (11077839577478395640345928763197218767898793877003011052396830159745843200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_26 h,accepted_27 h⟩
private noncomputable def tree24 : TapeTree := .centered (candidateRows ibox24) (candidateRows (FixedTape.midBox ibox24))
attribute [irreducible] tree24
private theorem sign_24 : 2*denominator*(computed denominator (FixedTape.midBox ibox24)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox24).gradient k).lo.natAbs ((computed denominator ibox24).gradient k).hi.natAbs : Int)*((ibox24 k).hi-(ibox24 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox24
    (computed denominator ibox24) (computed denominator (FixedTape.midBox ibox24))
    (by decide +kernel)
private theorem midpoint_even_24 : ∀ k, 2 ∣ (ibox24 k).lo+(ibox24 k).hi := by decide +kernel
private theorem accepted_24 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox24) tree24 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox24 midpoint_even_24
  simp only [tree24,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox24,candidate_valid h (FixedTape.midBox ibox24),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox24 78 (FixedTape.rowsAux denominator ibox24 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox24) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_24
private noncomputable def tree23 : TapeTree := .split 0 (((23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 : Int) : ℚ)/(denominator : ℚ)) tree24 tree25
attribute [irreducible] tree23
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox23 0 (23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 : Int) false,decode_split denominator ibox23 0 (23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_24 h,accepted_25 h⟩
private noncomputable def tree22 : TapeTree := .centered (candidateRows ibox22) (candidateRows (FixedTape.midBox ibox22))
attribute [irreducible] tree22
private theorem sign_22 : 2*denominator*(computed denominator (FixedTape.midBox ibox22)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox22).gradient k).lo.natAbs ((computed denominator ibox22).gradient k).hi.natAbs : Int)*((ibox22 k).hi-(ibox22 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox22
    (computed denominator ibox22) (computed denominator (FixedTape.midBox ibox22))
    (by decide +kernel)
private theorem midpoint_even_22 : ∀ k, 2 ∣ (ibox22 k).lo+(ibox22 k).hi := by decide +kernel
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox22 midpoint_even_22
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox22,candidate_valid h (FixedTape.midBox ibox22),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox22 78 (FixedTape.rowsAux denominator ibox22 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox22) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_22
private noncomputable def tree21 : TapeTree := .centered (candidateRows ibox21) (candidateRows (FixedTape.midBox ibox21))
attribute [irreducible] tree21
private theorem sign_21 : 2*denominator*(computed denominator (FixedTape.midBox ibox21)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox21).gradient k).lo.natAbs ((computed denominator ibox21).gradient k).hi.natAbs : Int)*((ibox21 k).hi-(ibox21 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox21
    (computed denominator ibox21) (computed denominator (FixedTape.midBox ibox21))
    (by decide +kernel)
private theorem midpoint_even_21 : ∀ k, 2 ∣ (ibox21 k).lo+(ibox21 k).hi := by decide +kernel
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox21 midpoint_even_21
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox21,candidate_valid h (FixedTape.midBox ibox21),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox21 78 (FixedTape.rowsAux denominator ibox21 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox21) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_21
private noncomputable def tree20 : TapeTree := .split 1 (((7912742555341711171675663402283727691356281340716436465997735828389888000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree21 tree22
attribute [irreducible] tree20
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox20 1 (7912742555341711171675663402283727691356281340716436465997735828389888000000000000000000000000 : Int) false,decode_split denominator ibox20 1 (7912742555341711171675663402283727691356281340716436465997735828389888000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_21 h,accepted_22 h⟩
private noncomputable def tree19 : TapeTree := .centered (candidateRows ibox19) (candidateRows (FixedTape.midBox ibox19))
attribute [irreducible] tree19
private theorem sign_19 : 2*denominator*(computed denominator (FixedTape.midBox ibox19)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox19).gradient k).lo.natAbs ((computed denominator ibox19).gradient k).hi.natAbs : Int)*((ibox19 k).hi-(ibox19 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox19
    (computed denominator ibox19) (computed denominator (FixedTape.midBox ibox19))
    (by decide +kernel)
private theorem midpoint_even_19 : ∀ k, 2 ∣ (ibox19 k).lo+(ibox19 k).hi := by decide +kernel
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox19 midpoint_even_19
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox19,candidate_valid h (FixedTape.midBox ibox19),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox19 78 (FixedTape.rowsAux denominator ibox19 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox19) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_19
private noncomputable def tree18 : TapeTree := .split 0 (((23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 : Int) : ℚ)/(denominator : ℚ)) tree19 tree20
attribute [irreducible] tree18
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox18 0 (23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 : Int) false,decode_split denominator ibox18 0 (23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_19 h,accepted_20 h⟩
private noncomputable def tree17 : TapeTree := .split 1 (((9495291066410053406010796082740473229627537608859723759197282994067865600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree18 tree23
attribute [irreducible] tree17
private theorem accepted_17 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox17) tree17 = true := by
  simp only [tree17,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox17 1 (9495291066410053406010796082740473229627537608859723759197282994067865600000000000000000000000 : Int) false,decode_split denominator ibox17 1 (9495291066410053406010796082740473229627537608859723759197282994067865600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_18 h,accepted_23 h⟩
private noncomputable def tree16 : TapeTree := .centered (candidateRows ibox16) (candidateRows (FixedTape.midBox ibox16))
attribute [irreducible] tree16
private theorem sign_16 : 2*denominator*(computed denominator (FixedTape.midBox ibox16)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox16).gradient k).lo.natAbs ((computed denominator ibox16).gradient k).hi.natAbs : Int)*((ibox16 k).hi-(ibox16 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox16
    (computed denominator ibox16) (computed denominator (FixedTape.midBox ibox16))
    (by decide +kernel)
private theorem midpoint_even_16 : ∀ k, 2 ∣ (ibox16 k).lo+(ibox16 k).hi := by decide +kernel
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox16 midpoint_even_16
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox16,candidate_valid h (FixedTape.midBox ibox16),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox16 78 (FixedTape.rowsAux denominator ibox16 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox16) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_16
private noncomputable def tree15 : TapeTree := .centered (candidateRows ibox15) (candidateRows (FixedTape.midBox ibox15))
attribute [irreducible] tree15
private theorem sign_15 : 2*denominator*(computed denominator (FixedTape.midBox ibox15)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox15).gradient k).lo.natAbs ((computed denominator ibox15).gradient k).hi.natAbs : Int)*((ibox15 k).hi-(ibox15 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox15
    (computed denominator ibox15) (computed denominator (FixedTape.midBox ibox15))
    (by decide +kernel)
private theorem midpoint_even_15 : ∀ k, 2 ∣ (ibox15 k).lo+(ibox15 k).hi := by decide +kernel
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox15 midpoint_even_15
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox15,candidate_valid h (FixedTape.midBox ibox15),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox15 78 (FixedTape.rowsAux denominator ibox15 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox15) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_15
private noncomputable def tree14 : TapeTree := .split 1 (((4747645533205026703005398041370236614813768804429861879598641497033932800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree15 tree16
attribute [irreducible] tree14
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox14 1 (4747645533205026703005398041370236614813768804429861879598641497033932800000000000000000000000 : Int) false,decode_split denominator ibox14 1 (4747645533205026703005398041370236614813768804429861879598641497033932800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_15 h,accepted_16 h⟩
private noncomputable def tree13 : TapeTree := .centered (candidateRows ibox13) (candidateRows (FixedTape.midBox ibox13))
attribute [irreducible] tree13
private theorem sign_13 : 2*denominator*(computed denominator (FixedTape.midBox ibox13)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox13).gradient k).lo.natAbs ((computed denominator ibox13).gradient k).hi.natAbs : Int)*((ibox13 k).hi-(ibox13 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox13
    (computed denominator ibox13) (computed denominator (FixedTape.midBox ibox13))
    (by decide +kernel)
private theorem midpoint_even_13 : ∀ k, 2 ∣ (ibox13 k).lo+(ibox13 k).hi := by decide +kernel
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox13 midpoint_even_13
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox13,candidate_valid h (FixedTape.midBox ibox13),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox13 78 (FixedTape.rowsAux denominator ibox13 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox13) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_13
private noncomputable def tree12 : TapeTree := .split 0 (((23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 : Int) : ℚ)/(denominator : ℚ)) tree13 tree14
attribute [irreducible] tree12
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox12 0 (23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 : Int) false,decode_split denominator ibox12 0 (23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_13 h,accepted_14 h⟩
private noncomputable def tree11 : TapeTree := .centered (candidateRows ibox11) (candidateRows (FixedTape.midBox ibox11))
attribute [irreducible] tree11
private theorem sign_11 : 2*denominator*(computed denominator (FixedTape.midBox ibox11)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox11).gradient k).lo.natAbs ((computed denominator ibox11).gradient k).hi.natAbs : Int)*((ibox11 k).hi-(ibox11 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox11
    (computed denominator ibox11) (computed denominator (FixedTape.midBox ibox11))
    (by decide +kernel)
private theorem midpoint_even_11 : ∀ k, 2 ∣ (ibox11 k).lo+(ibox11 k).hi := by decide +kernel
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox11 midpoint_even_11
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox11,candidate_valid h (FixedTape.midBox ibox11),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox11 78 (FixedTape.rowsAux denominator ibox11 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox11) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_11
private noncomputable def tree10 : TapeTree := .centered (candidateRows ibox10) (candidateRows (FixedTape.midBox ibox10))
attribute [irreducible] tree10
private theorem sign_10 : 2*denominator*(computed denominator (FixedTape.midBox ibox10)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox10).gradient k).lo.natAbs ((computed denominator ibox10).gradient k).hi.natAbs : Int)*((ibox10 k).hi-(ibox10 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox10
    (computed denominator ibox10) (computed denominator (FixedTape.midBox ibox10))
    (by decide +kernel)
private theorem midpoint_even_10 : ∀ k, 2 ∣ (ibox10 k).lo+(ibox10 k).hi := by decide +kernel
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox10 midpoint_even_10
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox10,candidate_valid h (FixedTape.midBox ibox10),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox10 78 (FixedTape.rowsAux denominator ibox10 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox10) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_10
private noncomputable def tree9 : TapeTree := .split 1 (((1582548511068342234335132680456745538271256268143287293199547165677977600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree10 tree11
attribute [irreducible] tree9
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox9 1 (1582548511068342234335132680456745538271256268143287293199547165677977600000000000000000000000 : Int) false,decode_split denominator ibox9 1 (1582548511068342234335132680456745538271256268143287293199547165677977600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_10 h,accepted_11 h⟩
private noncomputable def tree8 : TapeTree := .centered (candidateRows ibox8) (candidateRows (FixedTape.midBox ibox8))
attribute [irreducible] tree8
private theorem sign_8 : 2*denominator*(computed denominator (FixedTape.midBox ibox8)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox8).gradient k).lo.natAbs ((computed denominator ibox8).gradient k).hi.natAbs : Int)*((ibox8 k).hi-(ibox8 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox8
    (computed denominator ibox8) (computed denominator (FixedTape.midBox ibox8))
    (by decide +kernel)
private theorem midpoint_even_8 : ∀ k, 2 ∣ (ibox8 k).lo+(ibox8 k).hi := by decide +kernel
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox8 midpoint_even_8
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox8,candidate_valid h (FixedTape.midBox ibox8),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox8 78 (FixedTape.rowsAux denominator ibox8 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox8) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_8
private noncomputable def tree7 : TapeTree := .centered (candidateRows ibox7) (candidateRows (FixedTape.midBox ibox7))
attribute [irreducible] tree7
private theorem sign_7 : 2*denominator*(computed denominator (FixedTape.midBox ibox7)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox7).gradient k).lo.natAbs ((computed denominator ibox7).gradient k).hi.natAbs : Int)*((ibox7 k).hi-(ibox7 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox7
    (computed denominator ibox7) (computed denominator (FixedTape.midBox ibox7))
    (by decide +kernel)
private theorem midpoint_even_7 : ∀ k, 2 ∣ (ibox7 k).lo+(ibox7 k).hi := by decide +kernel
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox7 midpoint_even_7
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox7,candidate_valid h (FixedTape.midBox ibox7),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox7 78 (FixedTape.rowsAux denominator ibox7 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox7) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_7
private noncomputable def tree6 : TapeTree := .split 1 (((1582548511068342234335132680456745538271256268143287293199547165677977600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree8
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 1 (1582548511068342234335132680456745538271256268143287293199547165677977600000000000000000000000 : Int) false,decode_split denominator ibox6 1 (1582548511068342234335132680456745538271256268143287293199547165677977600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_7 h,accepted_8 h⟩
private noncomputable def tree5 : TapeTree := .split 0 (((23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 : Int) : ℚ)/(denominator : ℚ)) tree6 tree9
attribute [irreducible] tree5
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox5 0 (23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 : Int) false,decode_split denominator ibox5 0 (23606348623436105839524935053262312591283668910068322534896588231116388906425155028254720000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_6 h,accepted_9 h⟩
private noncomputable def tree4 : TapeTree := .split 1 (((3165097022136684468670265360913491076542512536286574586399094331355955200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree12
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 1 (3165097022136684468670265360913491076542512536286574586399094331355955200000000000000000000000 : Int) false,decode_split denominator ibox4 1 (3165097022136684468670265360913491076542512536286574586399094331355955200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_12 h⟩
private noncomputable def tree3 : TapeTree := .split 1 (((6330194044273368937340530721826982153085025072573149172798188662711910400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree17
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (6330194044273368937340530721826982153085025072573149172798188662711910400000000000000000000000 : Int) false,decode_split denominator ibox3 1 (6330194044273368937340530721826982153085025072573149172798188662711910400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_17 h⟩
private noncomputable def tree2 : TapeTree := .split 1 (((12660388088546737874681061443653964306170050145146298345596377325423820800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree28
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 1 (12660388088546737874681061443653964306170050145146298345596377325423820800000000000000000000000 : Int) false,decode_split denominator ibox2 1 (12660388088546737874681061443653964306170050145146298345596377325423820800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_28 h⟩
private noncomputable def tree1 : TapeTree := .face 3 true (candidateRows ibox1) tree2
attribute [irreducible] tree1
private theorem sign_1 : 0 ≤ ((computed denominator ibox1).gradient 3).lo := by decide +kernel
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox1,?_,accepted_2 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox1)).gradient 3).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox1).gradient 3).lo) denominator_positive).2 sign_1
private noncomputable def tree0 : TapeTree := .face 2 true (candidateRows ibox0) tree1
attribute [irreducible] tree0
private theorem sign_0 : 0 ≤ ((computed denominator ibox0).gradient 2).lo := by decide +kernel
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox0,?_,accepted_1 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox0)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox0).gradient 2).lo) denominator_positive).2 sign_0
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (4635416666666667/5000000000000000 : ℚ) (15/16 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 78 = e89 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (4635416666666667/5000000000000000 : ℚ) (15/16 : ℚ)) x → eval e89 x ≤ 0 := by
  have hb := h.child_4 tape 78 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell119_high_first_top

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell119_high_first_top
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((4635416666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((15/16 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 119 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 119 p)
    (hkb : ((15/16 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((4635416666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : bStar < a), firstResidual (0 : Fin 9) a p r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell119_high_first_top.cell_bound h.child_8 h.child_9 (Cell119_high_first_top.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell119_high_first_top
