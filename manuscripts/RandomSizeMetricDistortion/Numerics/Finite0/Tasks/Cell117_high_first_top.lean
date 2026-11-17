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
namespace Cell117_high_first_top
private noncomputable def qValues : Fin 2 → ℚ := ![(226451800342534439152434070079823212705/45565687446291975428117374979490889491 : ℚ),(-167440758533012062158575000000000000000/45565687446291975428117374979490889491 : ℚ)]
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
    priceLambda 117 p = ((226451800342534439152434070079823212705/45565687446291975428117374979490889491 : ℝ)+(-167440758533012062158575000000000000000/45565687446291975428117374979490889491 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell117,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 117 p = 0 := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell117,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e89 x = (x 0*(1-x 0))*(aPoint x+priceLambda 117 (x 0)*(HStar (yPoint x)-HStar (aPoint x))+priceTau 117 (x 0)*psiStar (rPoint x)+(cStar-aPoint x-eta (0 : Fin 9)*psiStar (aPoint x))-(cStar)) := by
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
    (hL : lambdaStar (x 0) = priceLambda 117 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 117 (x 0)) :
    (1)*eval e89 x = (x 0*(1-x 0))*(firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_neg (not_le.mpr ha),hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (29/32 : ℚ) (4583333333333333/5000000000000000 : ℚ)) x → eval e89 x ≤ 0)
    (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((29/32 : ℚ) : ℝ) < p ∧ p ≤ ((4583333333333333/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 117 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 117 p)
    (hkb : ((4583333333333333/5000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((29/32 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : bStar < a) :
    firstResidual (0 : Fin 9) a p r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxr⟩ := h5 (29/32 : ℚ) (4583333333333333/5000000000000000 : ℚ) bStar p a r hpcell hkb hr.2 hap hcase
  have hax : aPoint x = a := by simpa only [aPoint,rPoint] using hxa
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 117 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 117 (x 0) := by simpa only [hxp] using hT
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
.const (226451800342534439152434070079823212705/45565687446291975428117374979490889491 : ℚ),
.const (-167440758533012062158575000000000000000/45565687446291975428117374979490889491 : ℚ),
.mul 69 1,
.add 68 70,
.mul 1 34,
.add 7 32,
.const (-113609/200000 : ℚ),
.add 73 74,
.mul 75 72,
.mul 71 67,
.add 76 77]
private noncomputable def ssaQVals : Fin 16 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(-2840189/5000000 : ℚ),(113609/200000 : ℚ),(1085/4818 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ),(4818/3733 : ℚ),(145513/100000 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(226451800342534439152434070079823212705/45565687446291975428117374979490889491 : ℚ),(-167440758533012062158575000000000000000/45565687446291975428117374979490889491 : ℚ),(-113609/200000 : ℚ)]
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
private noncomputable def denominator : Int := 541079462723256467162346318933226269904373589350680776451272099119706931200000000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨490353263092951173365876351533236307100838565349054453658965339827234406400000000000000000000000,495989507496318392160186610805026269922587861356372718122093467481012923515193392019537920000000⟩,⟨0,541079462723256467162346318933226269904373589350680776451272099119706931200000000000000000000000⟩,⟨0,541079462723256467162346318933226269904373589350680776451272099119706931200000000000000000000000⟩,⟨0,541079462723256467162346318933226269904373589350680776451272099119706931200000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 2 true
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 3 true
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 1 270539731361628233581173159466613134952186794675340388225636049559853465600000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 135269865680814116790586579733306567476093397337670194112818024779926732800000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 1 67634932840407058395293289866653283738046698668835097056409012389963366400000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox5 1 33817466420203529197646644933326641869023349334417548528204506194981683200000000000000000000000 false
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox5 1 33817466420203529197646644933326641869023349334417548528204506194981683200000000000000000000000 true
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox4 1 67634932840407058395293289866653283738046698668835097056409012389963366400000000000000000000000 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox3 1 135269865680814116790586579733306567476093397337670194112818024779926732800000000000000000000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox9 1 202904798521221175185879869599959851214140096006505291169227037169890099200000000000000000000000 false
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox9 1 202904798521221175185879869599959851214140096006505291169227037169890099200000000000000000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox2 1 270539731361628233581173159466613134952186794675340388225636049559853465600000000000000000000000 true
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox12 1 405809597042442350371759739199919702428280192013010582338454074339780198400000000000000000000000 false
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox13 1 338174664202035291976466449333266418690233493344175485282045061949816832000000000000000000000000 false
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox13 1 338174664202035291976466449333266418690233493344175485282045061949816832000000000000000000000000 true
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox12 1 405809597042442350371759739199919702428280192013010582338454074339780198400000000000000000000000 true
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 1 473444529882849408767053029066572986166326890681845679394863086729743564800000000000000000000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox17 1 439627063462645879569406384133246344297303541347428130866658580534761881600000000000000000000000 false
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox17 1 439627063462645879569406384133246344297303541347428130866658580534761881600000000000000000000000 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox16 1 473444529882849408767053029066572986166326890681845679394863086729743564800000000000000000000000 true
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox20 1 507261996303052937964699673999899628035350240016263227923067592924725248000000000000000000000000 false
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox20 1 507261996303052937964699673999899628035350240016263227923067592924725248000000000000000000000000 true
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
private noncomputable def tree20 : TapeTree := .split 1 (((507261996303052937964699673999899628035350240016263227923067592924725248000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree21 tree22
attribute [irreducible] tree20
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox20 1 (507261996303052937964699673999899628035350240016263227923067592924725248000000000000000000000000 : Int) false,decode_split denominator ibox20 1 (507261996303052937964699673999899628035350240016263227923067592924725248000000000000000000000000 : Int) true]
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
private noncomputable def tree18 : TapeTree := .centered (candidateRows ibox18) (candidateRows (FixedTape.midBox ibox18))
attribute [irreducible] tree18
private theorem sign_18 : 2*denominator*(computed denominator (FixedTape.midBox ibox18)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox18).gradient k).lo.natAbs ((computed denominator ibox18).gradient k).hi.natAbs : Int)*((ibox18 k).hi-(ibox18 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox18
    (computed denominator ibox18) (computed denominator (FixedTape.midBox ibox18))
    (by decide +kernel)
private theorem midpoint_even_18 : ∀ k, 2 ∣ (ibox18 k).lo+(ibox18 k).hi := by decide +kernel
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox18 midpoint_even_18
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox18,candidate_valid h (FixedTape.midBox ibox18),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox18 78 (FixedTape.rowsAux denominator ibox18 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox18) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_18
private noncomputable def tree17 : TapeTree := .split 1 (((439627063462645879569406384133246344297303541347428130866658580534761881600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree18 tree19
attribute [irreducible] tree17
private theorem accepted_17 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox17) tree17 = true := by
  simp only [tree17,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox17 1 (439627063462645879569406384133246344297303541347428130866658580534761881600000000000000000000000 : Int) false,decode_split denominator ibox17 1 (439627063462645879569406384133246344297303541347428130866658580534761881600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_18 h,accepted_19 h⟩
private noncomputable def tree16 : TapeTree := .split 1 (((473444529882849408767053029066572986166326890681845679394863086729743564800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree20
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 1 (473444529882849408767053029066572986166326890681845679394863086729743564800000000000000000000000 : Int) false,decode_split denominator ibox16 1 (473444529882849408767053029066572986166326890681845679394863086729743564800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_17 h,accepted_20 h⟩
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
private noncomputable def tree14 : TapeTree := .centered (candidateRows ibox14) (candidateRows (FixedTape.midBox ibox14))
attribute [irreducible] tree14
private theorem sign_14 : 2*denominator*(computed denominator (FixedTape.midBox ibox14)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox14).gradient k).lo.natAbs ((computed denominator ibox14).gradient k).hi.natAbs : Int)*((ibox14 k).hi-(ibox14 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox14
    (computed denominator ibox14) (computed denominator (FixedTape.midBox ibox14))
    (by decide +kernel)
private theorem midpoint_even_14 : ∀ k, 2 ∣ (ibox14 k).lo+(ibox14 k).hi := by decide +kernel
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox14 midpoint_even_14
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox14,candidate_valid h (FixedTape.midBox ibox14),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox14 78 (FixedTape.rowsAux denominator ibox14 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox14) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_14
private noncomputable def tree13 : TapeTree := .split 1 (((338174664202035291976466449333266418690233493344175485282045061949816832000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree14 tree15
attribute [irreducible] tree13
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox13 1 (338174664202035291976466449333266418690233493344175485282045061949816832000000000000000000000000 : Int) false,decode_split denominator ibox13 1 (338174664202035291976466449333266418690233493344175485282045061949816832000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_14 h,accepted_15 h⟩
private noncomputable def tree12 : TapeTree := .split 1 (((405809597042442350371759739199919702428280192013010582338454074339780198400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree13 tree16
attribute [irreducible] tree12
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox12 1 (405809597042442350371759739199919702428280192013010582338454074339780198400000000000000000000000 : Int) false,decode_split denominator ibox12 1 (405809597042442350371759739199919702428280192013010582338454074339780198400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_13 h,accepted_16 h⟩
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
private noncomputable def tree9 : TapeTree := .split 1 (((202904798521221175185879869599959851214140096006505291169227037169890099200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree10 tree11
attribute [irreducible] tree9
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox9 1 (202904798521221175185879869599959851214140096006505291169227037169890099200000000000000000000000 : Int) false,decode_split denominator ibox9 1 (202904798521221175185879869599959851214140096006505291169227037169890099200000000000000000000000 : Int) true]
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
private noncomputable def tree6 : TapeTree := .centered (candidateRows ibox6) (candidateRows (FixedTape.midBox ibox6))
attribute [irreducible] tree6
private theorem sign_6 : 2*denominator*(computed denominator (FixedTape.midBox ibox6)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox6).gradient k).lo.natAbs ((computed denominator ibox6).gradient k).hi.natAbs : Int)*((ibox6 k).hi-(ibox6 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox6
    (computed denominator ibox6) (computed denominator (FixedTape.midBox ibox6))
    (by decide +kernel)
private theorem midpoint_even_6 : ∀ k, 2 ∣ (ibox6 k).lo+(ibox6 k).hi := by decide +kernel
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox6 midpoint_even_6
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox6,candidate_valid h (FixedTape.midBox ibox6),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox6 78 (FixedTape.rowsAux denominator ibox6 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox6) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_6
private noncomputable def tree5 : TapeTree := .split 1 (((33817466420203529197646644933326641869023349334417548528204506194981683200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree6 tree7
attribute [irreducible] tree5
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox5 1 (33817466420203529197646644933326641869023349334417548528204506194981683200000000000000000000000 : Int) false,decode_split denominator ibox5 1 (33817466420203529197646644933326641869023349334417548528204506194981683200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_6 h,accepted_7 h⟩
private noncomputable def tree4 : TapeTree := .split 1 (((67634932840407058395293289866653283738046698668835097056409012389963366400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree8
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 1 (67634932840407058395293289866653283738046698668835097056409012389963366400000000000000000000000 : Int) false,decode_split denominator ibox4 1 (67634932840407058395293289866653283738046698668835097056409012389963366400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_8 h⟩
private noncomputable def tree3 : TapeTree := .split 1 (((135269865680814116790586579733306567476093397337670194112818024779926732800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree9
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (135269865680814116790586579733306567476093397337670194112818024779926732800000000000000000000000 : Int) false,decode_split denominator ibox3 1 (135269865680814116790586579733306567476093397337670194112818024779926732800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_9 h⟩
private noncomputable def tree2 : TapeTree := .split 1 (((270539731361628233581173159466613134952186794675340388225636049559853465600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree12
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 78 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 1 (270539731361628233581173159466613134952186794675340388225636049559853465600000000000000000000000 : Int) false,decode_split denominator ibox2 1 (270539731361628233581173159466613134952186794675340388225636049559853465600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_12 h⟩
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
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (29/32 : ℚ) (4583333333333333/5000000000000000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 78 = e89 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (29/32 : ℚ) (4583333333333333/5000000000000000 : ℚ)) x → eval e89 x ≤ 0 := by
  have hb := h.child_4 tape 78 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell117_high_first_top

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell117_high_first_top
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((29/32 : ℚ) : ℝ) < p ∧ p ≤ ((4583333333333333/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 117 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 117 p)
    (hkb : ((4583333333333333/5000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((29/32 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : bStar < a), firstResidual (0 : Fin 9) a p r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell117_high_first_top.cell_bound h.child_8 h.child_9 (Cell117_high_first_top.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell117_high_first_top
