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
namespace Cell94_high_first_bottom
private noncomputable def qValues : Fin 2 → ℚ := ![(10503975350491275697898327585575312876/9323494627643469402458983775858378367 : ℚ),(7877373407782038227315000000000000000/9323494627643469402458983775858378367 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics25.e2 qValues
private noncomputable abbrev e7 : PolyExpr := SharedFiniteSemantics25.e7 qValues
private noncomputable abbrev e11 : PolyExpr := SharedFiniteSemantics25.e11 qValues
private noncomputable abbrev e15 : PolyExpr := SharedFiniteSemantics25.e15 qValues
private noncomputable abbrev e70 : PolyExpr := SharedFiniteSemantics25.e70 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics25.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics25.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics25.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics25.node_4 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics25.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics25.node_7 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics25.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics25.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics25.node_11 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics25.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics25.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics25.node_15 qValues
private noncomputable abbrev node_53 := SharedFiniteSemantics25.node_53 qValues
private noncomputable abbrev node_54 := SharedFiniteSemantics25.node_54 qValues
private noncomputable abbrev node_55 := SharedFiniteSemantics25.node_55 qValues
private noncomputable abbrev node_56 := SharedFiniteSemantics25.node_56 qValues
private noncomputable abbrev node_57 := SharedFiniteSemantics25.node_57 qValues
private noncomputable abbrev node_58 := SharedFiniteSemantics25.node_58 qValues
private noncomputable abbrev node_60 := SharedFiniteSemantics25.node_60 qValues
private noncomputable abbrev node_66 := SharedFiniteSemantics25.node_66 qValues
private noncomputable abbrev node_67 := SharedFiniteSemantics25.node_67 qValues
private noncomputable abbrev node_68 := SharedFiniteSemantics25.node_68 qValues
private noncomputable abbrev node_69 := SharedFiniteSemantics25.node_69 qValues
private noncomputable abbrev node_70 := SharedFiniteSemantics25.node_70 qValues
private noncomputable abbrev semantic_H_36 := SharedFiniteSemantics25.semantic_H_36 qValues
private noncomputable abbrev semantic_H_52 := SharedFiniteSemantics25.semantic_H_52 qValues
private noncomputable abbrev semantic_psi_86 := SharedFiniteSemantics25.semantic_psi_86 qValues
private noncomputable def aPoint (x : Fin 4 → ℝ) : ℝ := bStar*x 1
private noncomputable def rPoint (x : Fin 4 → ℝ) : ℝ := bStar+(1-bStar)*x 2
private noncomputable def yPoint (x : Fin 4 → ℝ) : ℝ := aPoint x+1-x 0
private theorem point_7 (x : Fin 4 → ℝ) : eval e7 x = aPoint x := by
  simp only [node_3,node_6,node_7] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_11 (x : Fin 4 → ℝ) : eval e11 x = rPoint x := by
  simp only [node_4,node_6,node_9,node_10,node_11] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_2 (x : Fin 4 → ℝ) : eval e2 x = x 0 := by
  simp only [node_2] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_15 (x : Fin 4 → ℝ) : eval e15 x = yPoint x := by
  simp only [node_1,node_2,node_3,node_6,node_7,node_13,node_14,node_15] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem price_lambda_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceLambda 94 p = ((10503975350491275697898327585575312876/9323494627643469402458983775858378367 : ℝ)+(7877373407782038227315000000000000000/9323494627643469402458983775858378367 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell94,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 94 p = 0 := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell94,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e70 x = (x 0*(1-x 0))*(aPoint x+priceLambda 94 (x 0)*(HStar (yPoint x)-HStar (aPoint x))+priceTau 94 (x 0)*psiStar (rPoint x)+(0)-(cStar)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_13,node_14,node_53,node_54,node_55,node_56,node_57,node_58,node_60,node_66,node_67,node_68,node_69,node_70,semantic_H_36,semantic_H_52,semantic_psi_86,point_7,point_11,point_2,point_15]
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
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) (ha : aPoint x ≤ bStar)
    (hL : lambdaStar (x 0) = priceLambda 94 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 94 (x 0)) :
    (1)*eval e70 x = (x 0*(1-x 0))*(firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (23/32 : ℚ) (3645833333333333/5000000000000000 : ℚ)) x → eval e70 x ≤ 0)
    (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((23/32 : ℚ) : ℝ) < p ∧ p ≤ ((3645833333333333/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 94 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 94 p)
    (hkb : ((3645833333333333/5000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((23/32 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ bStar) :
    firstResidual (0 : Fin 9) a p r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨x,hx,hxp,hxa,hxr⟩ := h4 (23/32 : ℚ) (3645833333333333/5000000000000000 : ℚ) bStar p a r hpcell hkb hr ha hap hcase
  have hcut : ¬(((3645833333333333/5000000000000000 : ℚ) : ℝ) ≤ bStar) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,if_neg hcut] using hxa
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,if_neg hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 94 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 94 (x 0) := by simpa only [hxp] using hT
  have hflag : aPoint x ≤ bStar := by simpa only [hax] using hcase
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e70 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
  rw [actual_identity hs x hpx hflag hLx hTx] at hv
  have hscale : 0 < x 0*(1-x 0) := mul_pos hpx.1 (sub_pos.mpr hpx.2)
  have hv : firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x) ≤ 0 := le_of_not_gt (fun hpos => (not_lt_of_ge hv) (mul_pos hscale hpos))
  simpa only [hxp,hax,hrx] using hv
private noncomputable def tape : List TapeOp := [
.const (1/1 : ℚ),
.var 0,
.var 1,
.const (2840189/5000000 : ℚ),
.mul 3 2,
.neg 1,
.add 0 5,
.add 4 6,
.const (1085/4818 : ℚ),
.mul 8 7,
.mul 7 7,
.const (19/146 : ℚ),
.mul 11 10,
.mul 7 10,
.const (35/438 : ℚ),
.mul 14 13,
.add 12 15,
.mul 10 10,
.mul 17 17,
.mul 18 18,
.mul 19 19,
.mul 7 20,
.const (1/66 : ℚ),
.mul 22 21,
.add 16 23,
.neg 24,
.add 9 25,
.const (4818/3733 : ℚ),
.mul 27 26,
.mul 8 4,
.mul 4 4,
.mul 11 30,
.mul 4 30,
.mul 14 32,
.add 31 33,
.mul 30 30,
.mul 35 35,
.mul 36 36,
.mul 37 37,
.mul 4 38,
.mul 22 39,
.add 34 40,
.neg 41,
.add 29 42,
.mul 27 43,
.neg 44,
.add 28 45,
.const (10503975350491275697898327585575312876/9323494627643469402458983775858378367 : ℚ),
.const (7877373407782038227315000000000000000/9323494627643469402458983775858378367 : ℚ),
.mul 48 1,
.add 47 49,
.mul 1 6,
.const (-113609/200000 : ℚ),
.add 4 52,
.mul 53 51,
.mul 50 46,
.add 54 55]
private noncomputable def ssaQVals : Fin 10 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(10503975350491275697898327585575312876/9323494627643469402458983775858378367 : ℚ),(7877373407782038227315000000000000000/9323494627643469402458983775858378367 : ℚ),(-113609/200000 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_75f0087db2b0bd70.p57 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_75f0087db2b0bd70.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 56 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_75f0087db2b0bd70.ssa_matches ssaQVals D B

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
private noncomputable def denominator : Int := 80519144144070206733567576290575538114903289389194899147255016884220723200000000000000000000000
private theorem denominator_positive : 0 < denominator := by decide +kernel
private noncomputable def candidateRows (B : Fin 4 → FixedTape.I) : List TapeBounds :=
  (FixedTape.rowsAux denominator B [] tape).map (FixedTape.decodeRow denominator)
private theorem root_in_range : 56 < tape.length := by decide +kernel
private theorem references_valid : tapeRefsValidAux 0 tape = true := by decide +kernel
private theorem candidate_valid (h : Needs) (B : Fin 4 → FixedTape.I) :
    tapeCheck (FixedTape.decodeBox denominator B) tape (candidateRows B) = true :=
  h.child_10.1 denominator denominator_positive B tape references_valid
private theorem candidate_root (B : Fin 4 → FixedTape.I) :
    (candidateRows B).getD 56 zeroTapeBounds = FixedTape.decodeRow denominator (computed denominator B) := by
  unfold candidateRows
  rw [←decode_zeroRow denominator,List.getD_map,ssa_matches]
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨57873134853550461089751695458851168020086739248483833762089543385533644800000000000000000000000,58711875938384520375283414773864214304278562474585406301320823865084334182998874385285120000000⟩,⟨0,80519144144070206733567576290575538114903289389194899147255016884220723200000000000000000000000⟩,⟨0,80519144144070206733567576290575538114903289389194899147255016884220723200000000000000000000000⟩,⟨0,80519144144070206733567576290575538114903289389194899147255016884220723200000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 2 true
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 3 true
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 1 40259572072035103366783788145287769057451644694597449573627508442110361600000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 1 10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox5 1 5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 false
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 1 2516223254502193960423986759080485566090727793412340598351719277631897600000000000000000000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox7 1 1258111627251096980211993379540242783045363896706170299175859638815948800000000000000000000000 false
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox8 0 58292505395967490732517555116357691162182650861534620031705183625308989491499437192642560000000 false
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox9 1 629055813625548490105996689770121391522681948353085149587929819407974400000000000000000000000 false
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox9 1 629055813625548490105996689770121391522681948353085149587929819407974400000000000000000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox8 0 58292505395967490732517555116357691162182650861534620031705183625308989491499437192642560000000 true
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox12 1 629055813625548490105996689770121391522681948353085149587929819407974400000000000000000000000 false
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox13 0 58502190667176005553900484945110952733230606668060013166513003745196661837249155788963840000000 false
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox13 0 58502190667176005553900484945110952733230606668060013166513003745196661837249155788963840000000 true
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox12 1 629055813625548490105996689770121391522681948353085149587929819407974400000000000000000000000 true
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 0 58502190667176005553900484945110952733230606668060013166513003745196661837249155788963840000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox16 0 58502190667176005553900484945110952733230606668060013166513003745196661837249155788963840000000 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox7 1 1258111627251096980211993379540242783045363896706170299175859638815948800000000000000000000000 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 0 58292505395967490732517555116357691162182650861534620031705183625308989491499437192642560000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox19 0 58292505395967490732517555116357691162182650861534620031705183625308989491499437192642560000000 true
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox21 1 1887167440876645470317990069310364174568045845059255448763789458223923200000000000000000000000 false
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox21 1 1887167440876645470317990069310364174568045845059255448763789458223923200000000000000000000000 true
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox6 1 2516223254502193960423986759080485566090727793412340598351719277631897600000000000000000000000 true
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox24 1 3774334881753290940635980138620728349136091690118510897527578916447846400000000000000000000000 false
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox25 0 58292505395967490732517555116357691162182650861534620031705183625308989491499437192642560000000 false
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox25 0 58292505395967490732517555116357691162182650861534620031705183625308989491499437192642560000000 true
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox27 1 3145279068127742450529983448850606957613409741765425747939649097039872000000000000000000000000 false
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox27 1 3145279068127742450529983448850606957613409741765425747939649097039872000000000000000000000000 true
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox24 1 3774334881753290940635980138620728349136091690118510897527578916447846400000000000000000000000 true
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox30 0 58292505395967490732517555116357691162182650861534620031705183625308989491499437192642560000000 false
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox30 0 58292505395967490732517555116357691162182650861534620031705183625308989491499437192642560000000 true
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox5 1 5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 true
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox33 1 7548669763506581881271960277241456698272183380237021795055157832895692800000000000000000000000 false
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox34 1 6290558136255484901059966897701213915226819483530851495879298194079744000000000000000000000000 false
private noncomputable def ibox36 : Fin 4 → FixedTape.I := splitI ibox34 1 6290558136255484901059966897701213915226819483530851495879298194079744000000000000000000000000 true
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox33 1 7548669763506581881271960277241456698272183380237021795055157832895692800000000000000000000000 true
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox4 1 10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 true
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox38 1 15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 false
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox39 1 12581116272510969802119933795402427830453638967061702991758596388159488000000000000000000000000 false
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox39 1 12581116272510969802119933795402427830453638967061702991758596388159488000000000000000000000000 true
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox38 1 15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 true
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox3 1 20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 true
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox43 1 30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 false
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox44 1 25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 false
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox44 1 25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 true
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox43 1 30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 true
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox2 1 40259572072035103366783788145287769057451644694597449573627508442110361600000000000000000000000 true
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox48 1 60389358108052655050175682217931653586177467041896174360441262663165542400000000000000000000000 false
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox49 1 50324465090043879208479735181609711321814555868246811967034385552637952000000000000000000000000 false
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox49 1 50324465090043879208479735181609711321814555868246811967034385552637952000000000000000000000000 true
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox48 1 60389358108052655050175682217931653586177467041896174360441262663165542400000000000000000000000 true
private noncomputable def tree52 : TapeTree := .centered (candidateRows ibox52) (candidateRows (FixedTape.midBox ibox52))
attribute [irreducible] tree52
private theorem sign_52 : 2*denominator*(computed denominator (FixedTape.midBox ibox52)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox52).gradient k).lo.natAbs ((computed denominator ibox52).gradient k).hi.natAbs : Int)*((ibox52 k).hi-(ibox52 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox52
    (computed denominator ibox52) (computed denominator (FixedTape.midBox ibox52))
    (by decide +kernel)
private theorem midpoint_even_52 : ∀ k, 2 ∣ (ibox52 k).lo+(ibox52 k).hi := by decide +kernel
private theorem accepted_52 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox52) tree52 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox52 midpoint_even_52
  simp only [tree52,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox52,candidate_valid h (FixedTape.midBox ibox52),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox52 56 (FixedTape.rowsAux denominator ibox52 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox52) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_52
private noncomputable def tree51 : TapeTree := .centered (candidateRows ibox51) (candidateRows (FixedTape.midBox ibox51))
attribute [irreducible] tree51
private theorem sign_51 : 2*denominator*(computed denominator (FixedTape.midBox ibox51)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox51).gradient k).lo.natAbs ((computed denominator ibox51).gradient k).hi.natAbs : Int)*((ibox51 k).hi-(ibox51 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox51
    (computed denominator ibox51) (computed denominator (FixedTape.midBox ibox51))
    (by decide +kernel)
private theorem midpoint_even_51 : ∀ k, 2 ∣ (ibox51 k).lo+(ibox51 k).hi := by decide +kernel
private theorem accepted_51 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox51) tree51 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox51 midpoint_even_51
  simp only [tree51,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox51,candidate_valid h (FixedTape.midBox ibox51),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox51 56 (FixedTape.rowsAux denominator ibox51 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox51) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_51
private noncomputable def tree50 : TapeTree := .centered (candidateRows ibox50) (candidateRows (FixedTape.midBox ibox50))
attribute [irreducible] tree50
private theorem sign_50 : 2*denominator*(computed denominator (FixedTape.midBox ibox50)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox50).gradient k).lo.natAbs ((computed denominator ibox50).gradient k).hi.natAbs : Int)*((ibox50 k).hi-(ibox50 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox50
    (computed denominator ibox50) (computed denominator (FixedTape.midBox ibox50))
    (by decide +kernel)
private theorem midpoint_even_50 : ∀ k, 2 ∣ (ibox50 k).lo+(ibox50 k).hi := by decide +kernel
private theorem accepted_50 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox50) tree50 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox50 midpoint_even_50
  simp only [tree50,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox50,candidate_valid h (FixedTape.midBox ibox50),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox50 56 (FixedTape.rowsAux denominator ibox50 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox50) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_50
private noncomputable def tree49 : TapeTree := .split 1 (((50324465090043879208479735181609711321814555868246811967034385552637952000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree50 tree51
attribute [irreducible] tree49
private theorem accepted_49 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox49) tree49 = true := by
  simp only [tree49,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox49 1 (50324465090043879208479735181609711321814555868246811967034385552637952000000000000000000000000 : Int) false,decode_split denominator ibox49 1 (50324465090043879208479735181609711321814555868246811967034385552637952000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_50 h,accepted_51 h⟩
private noncomputable def tree48 : TapeTree := .split 1 (((60389358108052655050175682217931653586177467041896174360441262663165542400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree49 tree52
attribute [irreducible] tree48
private theorem accepted_48 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox48) tree48 = true := by
  simp only [tree48,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox48 1 (60389358108052655050175682217931653586177467041896174360441262663165542400000000000000000000000 : Int) false,decode_split denominator ibox48 1 (60389358108052655050175682217931653586177467041896174360441262663165542400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_49 h,accepted_52 h⟩
private noncomputable def tree47 : TapeTree := .centered (candidateRows ibox47) (candidateRows (FixedTape.midBox ibox47))
attribute [irreducible] tree47
private theorem sign_47 : 2*denominator*(computed denominator (FixedTape.midBox ibox47)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox47).gradient k).lo.natAbs ((computed denominator ibox47).gradient k).hi.natAbs : Int)*((ibox47 k).hi-(ibox47 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox47
    (computed denominator ibox47) (computed denominator (FixedTape.midBox ibox47))
    (by decide +kernel)
private theorem midpoint_even_47 : ∀ k, 2 ∣ (ibox47 k).lo+(ibox47 k).hi := by decide +kernel
private theorem accepted_47 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox47) tree47 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox47 midpoint_even_47
  simp only [tree47,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox47,candidate_valid h (FixedTape.midBox ibox47),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox47 56 (FixedTape.rowsAux denominator ibox47 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox47) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_47
private noncomputable def tree46 : TapeTree := .centered (candidateRows ibox46) (candidateRows (FixedTape.midBox ibox46))
attribute [irreducible] tree46
private theorem sign_46 : 2*denominator*(computed denominator (FixedTape.midBox ibox46)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox46).gradient k).lo.natAbs ((computed denominator ibox46).gradient k).hi.natAbs : Int)*((ibox46 k).hi-(ibox46 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox46
    (computed denominator ibox46) (computed denominator (FixedTape.midBox ibox46))
    (by decide +kernel)
private theorem midpoint_even_46 : ∀ k, 2 ∣ (ibox46 k).lo+(ibox46 k).hi := by decide +kernel
private theorem accepted_46 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox46) tree46 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox46 midpoint_even_46
  simp only [tree46,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox46,candidate_valid h (FixedTape.midBox ibox46),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox46 56 (FixedTape.rowsAux denominator ibox46 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox46) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_46
private noncomputable def tree45 : TapeTree := .centered (candidateRows ibox45) (candidateRows (FixedTape.midBox ibox45))
attribute [irreducible] tree45
private theorem sign_45 : 2*denominator*(computed denominator (FixedTape.midBox ibox45)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox45).gradient k).lo.natAbs ((computed denominator ibox45).gradient k).hi.natAbs : Int)*((ibox45 k).hi-(ibox45 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox45
    (computed denominator ibox45) (computed denominator (FixedTape.midBox ibox45))
    (by decide +kernel)
private theorem midpoint_even_45 : ∀ k, 2 ∣ (ibox45 k).lo+(ibox45 k).hi := by decide +kernel
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox45 midpoint_even_45
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox45,candidate_valid h (FixedTape.midBox ibox45),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox45 56 (FixedTape.rowsAux denominator ibox45 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox45) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_45
private noncomputable def tree44 : TapeTree := .split 1 (((25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree45 tree46
attribute [irreducible] tree44
private theorem accepted_44 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox44) tree44 = true := by
  simp only [tree44,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox44 1 (25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) false,decode_split denominator ibox44 1 (25162232545021939604239867590804855660907277934123405983517192776318976000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_45 h,accepted_46 h⟩
private noncomputable def tree43 : TapeTree := .split 1 (((30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree44 tree47
attribute [irreducible] tree43
private theorem accepted_43 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox43) tree43 = true := by
  simp only [tree43,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox43 1 (30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) false,decode_split denominator ibox43 1 (30194679054026327525087841108965826793088733520948087180220631331582771200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_44 h,accepted_47 h⟩
private noncomputable def tree42 : TapeTree := .centered (candidateRows ibox42) (candidateRows (FixedTape.midBox ibox42))
attribute [irreducible] tree42
private theorem sign_42 : 2*denominator*(computed denominator (FixedTape.midBox ibox42)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox42).gradient k).lo.natAbs ((computed denominator ibox42).gradient k).hi.natAbs : Int)*((ibox42 k).hi-(ibox42 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox42
    (computed denominator ibox42) (computed denominator (FixedTape.midBox ibox42))
    (by decide +kernel)
private theorem midpoint_even_42 : ∀ k, 2 ∣ (ibox42 k).lo+(ibox42 k).hi := by decide +kernel
private theorem accepted_42 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox42) tree42 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox42 midpoint_even_42
  simp only [tree42,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox42,candidate_valid h (FixedTape.midBox ibox42),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox42 56 (FixedTape.rowsAux denominator ibox42 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox42) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_42
private noncomputable def tree41 : TapeTree := .centered (candidateRows ibox41) (candidateRows (FixedTape.midBox ibox41))
attribute [irreducible] tree41
private theorem sign_41 : 2*denominator*(computed denominator (FixedTape.midBox ibox41)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox41).gradient k).lo.natAbs ((computed denominator ibox41).gradient k).hi.natAbs : Int)*((ibox41 k).hi-(ibox41 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox41
    (computed denominator ibox41) (computed denominator (FixedTape.midBox ibox41))
    (by decide +kernel)
private theorem midpoint_even_41 : ∀ k, 2 ∣ (ibox41 k).lo+(ibox41 k).hi := by decide +kernel
private theorem accepted_41 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox41) tree41 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox41 midpoint_even_41
  simp only [tree41,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox41,candidate_valid h (FixedTape.midBox ibox41),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox41 56 (FixedTape.rowsAux denominator ibox41 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox41) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_41
private noncomputable def tree40 : TapeTree := .centered (candidateRows ibox40) (candidateRows (FixedTape.midBox ibox40))
attribute [irreducible] tree40
private theorem sign_40 : 2*denominator*(computed denominator (FixedTape.midBox ibox40)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox40).gradient k).lo.natAbs ((computed denominator ibox40).gradient k).hi.natAbs : Int)*((ibox40 k).hi-(ibox40 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox40
    (computed denominator ibox40) (computed denominator (FixedTape.midBox ibox40))
    (by decide +kernel)
private theorem midpoint_even_40 : ∀ k, 2 ∣ (ibox40 k).lo+(ibox40 k).hi := by decide +kernel
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox40 midpoint_even_40
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox40,candidate_valid h (FixedTape.midBox ibox40),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox40 56 (FixedTape.rowsAux denominator ibox40 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox40) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_40
private noncomputable def tree39 : TapeTree := .split 1 (((12581116272510969802119933795402427830453638967061702991758596388159488000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree40 tree41
attribute [irreducible] tree39
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox39 1 (12581116272510969802119933795402427830453638967061702991758596388159488000000000000000000000000 : Int) false,decode_split denominator ibox39 1 (12581116272510969802119933795402427830453638967061702991758596388159488000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_40 h,accepted_41 h⟩
private noncomputable def tree38 : TapeTree := .split 1 (((15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree39 tree42
attribute [irreducible] tree38
private theorem accepted_38 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox38) tree38 = true := by
  simp only [tree38,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox38 1 (15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) false,decode_split denominator ibox38 1 (15097339527013163762543920554482913396544366760474043590110315665791385600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_39 h,accepted_42 h⟩
private noncomputable def tree37 : TapeTree := .centered (candidateRows ibox37) (candidateRows (FixedTape.midBox ibox37))
attribute [irreducible] tree37
private theorem sign_37 : 2*denominator*(computed denominator (FixedTape.midBox ibox37)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox37).gradient k).lo.natAbs ((computed denominator ibox37).gradient k).hi.natAbs : Int)*((ibox37 k).hi-(ibox37 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox37
    (computed denominator ibox37) (computed denominator (FixedTape.midBox ibox37))
    (by decide +kernel)
private theorem midpoint_even_37 : ∀ k, 2 ∣ (ibox37 k).lo+(ibox37 k).hi := by decide +kernel
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox37 midpoint_even_37
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox37,candidate_valid h (FixedTape.midBox ibox37),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox37 56 (FixedTape.rowsAux denominator ibox37 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox37) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_37
private noncomputable def tree36 : TapeTree := .centered (candidateRows ibox36) (candidateRows (FixedTape.midBox ibox36))
attribute [irreducible] tree36
private theorem sign_36 : 2*denominator*(computed denominator (FixedTape.midBox ibox36)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox36).gradient k).lo.natAbs ((computed denominator ibox36).gradient k).hi.natAbs : Int)*((ibox36 k).hi-(ibox36 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox36
    (computed denominator ibox36) (computed denominator (FixedTape.midBox ibox36))
    (by decide +kernel)
private theorem midpoint_even_36 : ∀ k, 2 ∣ (ibox36 k).lo+(ibox36 k).hi := by decide +kernel
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox36 midpoint_even_36
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox36,candidate_valid h (FixedTape.midBox ibox36),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox36 56 (FixedTape.rowsAux denominator ibox36 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox36) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_36
private noncomputable def tree35 : TapeTree := .centered (candidateRows ibox35) (candidateRows (FixedTape.midBox ibox35))
attribute [irreducible] tree35
private theorem sign_35 : 2*denominator*(computed denominator (FixedTape.midBox ibox35)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox35).gradient k).lo.natAbs ((computed denominator ibox35).gradient k).hi.natAbs : Int)*((ibox35 k).hi-(ibox35 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox35
    (computed denominator ibox35) (computed denominator (FixedTape.midBox ibox35))
    (by decide +kernel)
private theorem midpoint_even_35 : ∀ k, 2 ∣ (ibox35 k).lo+(ibox35 k).hi := by decide +kernel
private theorem accepted_35 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox35) tree35 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox35 midpoint_even_35
  simp only [tree35,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox35,candidate_valid h (FixedTape.midBox ibox35),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox35 56 (FixedTape.rowsAux denominator ibox35 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox35) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_35
private noncomputable def tree34 : TapeTree := .split 1 (((6290558136255484901059966897701213915226819483530851495879298194079744000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree35 tree36
attribute [irreducible] tree34
private theorem accepted_34 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox34) tree34 = true := by
  simp only [tree34,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox34 1 (6290558136255484901059966897701213915226819483530851495879298194079744000000000000000000000000 : Int) false,decode_split denominator ibox34 1 (6290558136255484901059966897701213915226819483530851495879298194079744000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_35 h,accepted_36 h⟩
private noncomputable def tree33 : TapeTree := .split 1 (((7548669763506581881271960277241456698272183380237021795055157832895692800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree34 tree37
attribute [irreducible] tree33
private theorem accepted_33 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox33) tree33 = true := by
  simp only [tree33,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox33 1 (7548669763506581881271960277241456698272183380237021795055157832895692800000000000000000000000 : Int) false,decode_split denominator ibox33 1 (7548669763506581881271960277241456698272183380237021795055157832895692800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_34 h,accepted_37 h⟩
private noncomputable def tree32 : TapeTree := .centered (candidateRows ibox32) (candidateRows (FixedTape.midBox ibox32))
attribute [irreducible] tree32
private theorem sign_32 : 2*denominator*(computed denominator (FixedTape.midBox ibox32)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox32).gradient k).lo.natAbs ((computed denominator ibox32).gradient k).hi.natAbs : Int)*((ibox32 k).hi-(ibox32 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox32
    (computed denominator ibox32) (computed denominator (FixedTape.midBox ibox32))
    (by decide +kernel)
private theorem midpoint_even_32 : ∀ k, 2 ∣ (ibox32 k).lo+(ibox32 k).hi := by decide +kernel
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox32 midpoint_even_32
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox32,candidate_valid h (FixedTape.midBox ibox32),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox32 56 (FixedTape.rowsAux denominator ibox32 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox32) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_32
private noncomputable def tree31 : TapeTree := .centered (candidateRows ibox31) (candidateRows (FixedTape.midBox ibox31))
attribute [irreducible] tree31
private theorem sign_31 : 2*denominator*(computed denominator (FixedTape.midBox ibox31)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox31).gradient k).lo.natAbs ((computed denominator ibox31).gradient k).hi.natAbs : Int)*((ibox31 k).hi-(ibox31 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox31
    (computed denominator ibox31) (computed denominator (FixedTape.midBox ibox31))
    (by decide +kernel)
private theorem midpoint_even_31 : ∀ k, 2 ∣ (ibox31 k).lo+(ibox31 k).hi := by decide +kernel
private theorem accepted_31 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox31) tree31 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox31 midpoint_even_31
  simp only [tree31,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox31,candidate_valid h (FixedTape.midBox ibox31),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox31 56 (FixedTape.rowsAux denominator ibox31 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox31) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_31
private noncomputable def tree30 : TapeTree := .split 0 (((58292505395967490732517555116357691162182650861534620031705183625308989491499437192642560000000 : Int) : ℚ)/(denominator : ℚ)) tree31 tree32
attribute [irreducible] tree30
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox30 0 (58292505395967490732517555116357691162182650861534620031705183625308989491499437192642560000000 : Int) false,decode_split denominator ibox30 0 (58292505395967490732517555116357691162182650861534620031705183625308989491499437192642560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_31 h,accepted_32 h⟩
private noncomputable def tree29 : TapeTree := .centered (candidateRows ibox29) (candidateRows (FixedTape.midBox ibox29))
attribute [irreducible] tree29
private theorem sign_29 : 2*denominator*(computed denominator (FixedTape.midBox ibox29)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox29).gradient k).lo.natAbs ((computed denominator ibox29).gradient k).hi.natAbs : Int)*((ibox29 k).hi-(ibox29 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox29
    (computed denominator ibox29) (computed denominator (FixedTape.midBox ibox29))
    (by decide +kernel)
private theorem midpoint_even_29 : ∀ k, 2 ∣ (ibox29 k).lo+(ibox29 k).hi := by decide +kernel
private theorem accepted_29 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox29) tree29 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox29 midpoint_even_29
  simp only [tree29,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox29,candidate_valid h (FixedTape.midBox ibox29),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox29 56 (FixedTape.rowsAux denominator ibox29 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox29) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_29
private noncomputable def tree28 : TapeTree := .centered (candidateRows ibox28) (candidateRows (FixedTape.midBox ibox28))
attribute [irreducible] tree28
private theorem sign_28 : 2*denominator*(computed denominator (FixedTape.midBox ibox28)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox28).gradient k).lo.natAbs ((computed denominator ibox28).gradient k).hi.natAbs : Int)*((ibox28 k).hi-(ibox28 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox28
    (computed denominator ibox28) (computed denominator (FixedTape.midBox ibox28))
    (by decide +kernel)
private theorem midpoint_even_28 : ∀ k, 2 ∣ (ibox28 k).lo+(ibox28 k).hi := by decide +kernel
private theorem accepted_28 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox28) tree28 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox28 midpoint_even_28
  simp only [tree28,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox28,candidate_valid h (FixedTape.midBox ibox28),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox28 56 (FixedTape.rowsAux denominator ibox28 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox28) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_28
private noncomputable def tree27 : TapeTree := .split 1 (((3145279068127742450529983448850606957613409741765425747939649097039872000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree28 tree29
attribute [irreducible] tree27
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox27 1 (3145279068127742450529983448850606957613409741765425747939649097039872000000000000000000000000 : Int) false,decode_split denominator ibox27 1 (3145279068127742450529983448850606957613409741765425747939649097039872000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_28 h,accepted_29 h⟩
private noncomputable def tree26 : TapeTree := .centered (candidateRows ibox26) (candidateRows (FixedTape.midBox ibox26))
attribute [irreducible] tree26
private theorem sign_26 : 2*denominator*(computed denominator (FixedTape.midBox ibox26)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox26).gradient k).lo.natAbs ((computed denominator ibox26).gradient k).hi.natAbs : Int)*((ibox26 k).hi-(ibox26 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox26
    (computed denominator ibox26) (computed denominator (FixedTape.midBox ibox26))
    (by decide +kernel)
private theorem midpoint_even_26 : ∀ k, 2 ∣ (ibox26 k).lo+(ibox26 k).hi := by decide +kernel
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox26 midpoint_even_26
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox26,candidate_valid h (FixedTape.midBox ibox26),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox26 56 (FixedTape.rowsAux denominator ibox26 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox26) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_26
private noncomputable def tree25 : TapeTree := .split 0 (((58292505395967490732517555116357691162182650861534620031705183625308989491499437192642560000000 : Int) : ℚ)/(denominator : ℚ)) tree26 tree27
attribute [irreducible] tree25
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox25 0 (58292505395967490732517555116357691162182650861534620031705183625308989491499437192642560000000 : Int) false,decode_split denominator ibox25 0 (58292505395967490732517555116357691162182650861534620031705183625308989491499437192642560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_26 h,accepted_27 h⟩
private noncomputable def tree24 : TapeTree := .split 1 (((3774334881753290940635980138620728349136091690118510897527578916447846400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree25 tree30
attribute [irreducible] tree24
private theorem accepted_24 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox24) tree24 = true := by
  simp only [tree24,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox24 1 (3774334881753290940635980138620728349136091690118510897527578916447846400000000000000000000000 : Int) false,decode_split denominator ibox24 1 (3774334881753290940635980138620728349136091690118510897527578916447846400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_25 h,accepted_30 h⟩
private noncomputable def tree23 : TapeTree := .centered (candidateRows ibox23) (candidateRows (FixedTape.midBox ibox23))
attribute [irreducible] tree23
private theorem sign_23 : 2*denominator*(computed denominator (FixedTape.midBox ibox23)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox23).gradient k).lo.natAbs ((computed denominator ibox23).gradient k).hi.natAbs : Int)*((ibox23 k).hi-(ibox23 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox23
    (computed denominator ibox23) (computed denominator (FixedTape.midBox ibox23))
    (by decide +kernel)
private theorem midpoint_even_23 : ∀ k, 2 ∣ (ibox23 k).lo+(ibox23 k).hi := by decide +kernel
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox23 midpoint_even_23
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox23,candidate_valid h (FixedTape.midBox ibox23),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox23 56 (FixedTape.rowsAux denominator ibox23 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox23) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_23
private noncomputable def tree22 : TapeTree := .centered (candidateRows ibox22) (candidateRows (FixedTape.midBox ibox22))
attribute [irreducible] tree22
private theorem sign_22 : 2*denominator*(computed denominator (FixedTape.midBox ibox22)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox22).gradient k).lo.natAbs ((computed denominator ibox22).gradient k).hi.natAbs : Int)*((ibox22 k).hi-(ibox22 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox22
    (computed denominator ibox22) (computed denominator (FixedTape.midBox ibox22))
    (by decide +kernel)
private theorem midpoint_even_22 : ∀ k, 2 ∣ (ibox22 k).lo+(ibox22 k).hi := by decide +kernel
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox22 midpoint_even_22
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox22,candidate_valid h (FixedTape.midBox ibox22),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox22 56 (FixedTape.rowsAux denominator ibox22 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox22) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_22
private noncomputable def tree21 : TapeTree := .split 1 (((1887167440876645470317990069310364174568045845059255448763789458223923200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree22 tree23
attribute [irreducible] tree21
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox21 1 (1887167440876645470317990069310364174568045845059255448763789458223923200000000000000000000000 : Int) false,decode_split denominator ibox21 1 (1887167440876645470317990069310364174568045845059255448763789458223923200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_22 h,accepted_23 h⟩
private noncomputable def tree20 : TapeTree := .centered (candidateRows ibox20) (candidateRows (FixedTape.midBox ibox20))
attribute [irreducible] tree20
private theorem sign_20 : 2*denominator*(computed denominator (FixedTape.midBox ibox20)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox20).gradient k).lo.natAbs ((computed denominator ibox20).gradient k).hi.natAbs : Int)*((ibox20 k).hi-(ibox20 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox20
    (computed denominator ibox20) (computed denominator (FixedTape.midBox ibox20))
    (by decide +kernel)
private theorem midpoint_even_20 : ∀ k, 2 ∣ (ibox20 k).lo+(ibox20 k).hi := by decide +kernel
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox20 midpoint_even_20
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox20,candidate_valid h (FixedTape.midBox ibox20),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox20 56 (FixedTape.rowsAux denominator ibox20 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox20) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_20
private noncomputable def tree19 : TapeTree := .split 0 (((58292505395967490732517555116357691162182650861534620031705183625308989491499437192642560000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree21
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 0 (58292505395967490732517555116357691162182650861534620031705183625308989491499437192642560000000 : Int) false,decode_split denominator ibox19 0 (58292505395967490732517555116357691162182650861534620031705183625308989491499437192642560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_20 h,accepted_21 h⟩
private noncomputable def tree18 : TapeTree := .centered (candidateRows ibox18) (candidateRows (FixedTape.midBox ibox18))
attribute [irreducible] tree18
private theorem sign_18 : 2*denominator*(computed denominator (FixedTape.midBox ibox18)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox18).gradient k).lo.natAbs ((computed denominator ibox18).gradient k).hi.natAbs : Int)*((ibox18 k).hi-(ibox18 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox18
    (computed denominator ibox18) (computed denominator (FixedTape.midBox ibox18))
    (by decide +kernel)
private theorem midpoint_even_18 : ∀ k, 2 ∣ (ibox18 k).lo+(ibox18 k).hi := by decide +kernel
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox18 midpoint_even_18
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox18,candidate_valid h (FixedTape.midBox ibox18),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox18 56 (FixedTape.rowsAux denominator ibox18 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox18) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_18
private noncomputable def tree17 : TapeTree := .centered (candidateRows ibox17) (candidateRows (FixedTape.midBox ibox17))
attribute [irreducible] tree17
private theorem sign_17 : 2*denominator*(computed denominator (FixedTape.midBox ibox17)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox17).gradient k).lo.natAbs ((computed denominator ibox17).gradient k).hi.natAbs : Int)*((ibox17 k).hi-(ibox17 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox17
    (computed denominator ibox17) (computed denominator (FixedTape.midBox ibox17))
    (by decide +kernel)
private theorem midpoint_even_17 : ∀ k, 2 ∣ (ibox17 k).lo+(ibox17 k).hi := by decide +kernel
private theorem accepted_17 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox17) tree17 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox17 midpoint_even_17
  simp only [tree17,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox17,candidate_valid h (FixedTape.midBox ibox17),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox17 56 (FixedTape.rowsAux denominator ibox17 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox17) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_17
private noncomputable def tree16 : TapeTree := .split 0 (((58502190667176005553900484945110952733230606668060013166513003745196661837249155788963840000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree18
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 0 (58502190667176005553900484945110952733230606668060013166513003745196661837249155788963840000000 : Int) false,decode_split denominator ibox16 0 (58502190667176005553900484945110952733230606668060013166513003745196661837249155788963840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_17 h,accepted_18 h⟩
private noncomputable def tree15 : TapeTree := .centered (candidateRows ibox15) (candidateRows (FixedTape.midBox ibox15))
attribute [irreducible] tree15
private theorem sign_15 : 2*denominator*(computed denominator (FixedTape.midBox ibox15)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox15).gradient k).lo.natAbs ((computed denominator ibox15).gradient k).hi.natAbs : Int)*((ibox15 k).hi-(ibox15 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox15
    (computed denominator ibox15) (computed denominator (FixedTape.midBox ibox15))
    (by decide +kernel)
private theorem midpoint_even_15 : ∀ k, 2 ∣ (ibox15 k).lo+(ibox15 k).hi := by decide +kernel
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox15 midpoint_even_15
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox15,candidate_valid h (FixedTape.midBox ibox15),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox15 56 (FixedTape.rowsAux denominator ibox15 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox15) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_15
private noncomputable def tree14 : TapeTree := .centered (candidateRows ibox14) (candidateRows (FixedTape.midBox ibox14))
attribute [irreducible] tree14
private theorem sign_14 : 2*denominator*(computed denominator (FixedTape.midBox ibox14)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox14).gradient k).lo.natAbs ((computed denominator ibox14).gradient k).hi.natAbs : Int)*((ibox14 k).hi-(ibox14 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox14
    (computed denominator ibox14) (computed denominator (FixedTape.midBox ibox14))
    (by decide +kernel)
private theorem midpoint_even_14 : ∀ k, 2 ∣ (ibox14 k).lo+(ibox14 k).hi := by decide +kernel
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox14 midpoint_even_14
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox14,candidate_valid h (FixedTape.midBox ibox14),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox14 56 (FixedTape.rowsAux denominator ibox14 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox14) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_14
private noncomputable def tree13 : TapeTree := .split 0 (((58502190667176005553900484945110952733230606668060013166513003745196661837249155788963840000000 : Int) : ℚ)/(denominator : ℚ)) tree14 tree15
attribute [irreducible] tree13
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox13 0 (58502190667176005553900484945110952733230606668060013166513003745196661837249155788963840000000 : Int) false,decode_split denominator ibox13 0 (58502190667176005553900484945110952733230606668060013166513003745196661837249155788963840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_14 h,accepted_15 h⟩
private noncomputable def tree12 : TapeTree := .split 1 (((629055813625548490105996689770121391522681948353085149587929819407974400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree13 tree16
attribute [irreducible] tree12
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox12 1 (629055813625548490105996689770121391522681948353085149587929819407974400000000000000000000000 : Int) false,decode_split denominator ibox12 1 (629055813625548490105996689770121391522681948353085149587929819407974400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_13 h,accepted_16 h⟩
private noncomputable def tree11 : TapeTree := .centered (candidateRows ibox11) (candidateRows (FixedTape.midBox ibox11))
attribute [irreducible] tree11
private theorem sign_11 : 2*denominator*(computed denominator (FixedTape.midBox ibox11)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox11).gradient k).lo.natAbs ((computed denominator ibox11).gradient k).hi.natAbs : Int)*((ibox11 k).hi-(ibox11 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox11
    (computed denominator ibox11) (computed denominator (FixedTape.midBox ibox11))
    (by decide +kernel)
private theorem midpoint_even_11 : ∀ k, 2 ∣ (ibox11 k).lo+(ibox11 k).hi := by decide +kernel
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox11 midpoint_even_11
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox11,candidate_valid h (FixedTape.midBox ibox11),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox11 56 (FixedTape.rowsAux denominator ibox11 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox11) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_11
private noncomputable def tree10 : TapeTree := .centered (candidateRows ibox10) (candidateRows (FixedTape.midBox ibox10))
attribute [irreducible] tree10
private theorem sign_10 : 2*denominator*(computed denominator (FixedTape.midBox ibox10)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox10).gradient k).lo.natAbs ((computed denominator ibox10).gradient k).hi.natAbs : Int)*((ibox10 k).hi-(ibox10 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox10
    (computed denominator ibox10) (computed denominator (FixedTape.midBox ibox10))
    (by decide +kernel)
private theorem midpoint_even_10 : ∀ k, 2 ∣ (ibox10 k).lo+(ibox10 k).hi := by decide +kernel
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox10 midpoint_even_10
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox10,candidate_valid h (FixedTape.midBox ibox10),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox10 56 (FixedTape.rowsAux denominator ibox10 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox10) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_10
private noncomputable def tree9 : TapeTree := .split 1 (((629055813625548490105996689770121391522681948353085149587929819407974400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree10 tree11
attribute [irreducible] tree9
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox9 1 (629055813625548490105996689770121391522681948353085149587929819407974400000000000000000000000 : Int) false,decode_split denominator ibox9 1 (629055813625548490105996689770121391522681948353085149587929819407974400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_10 h,accepted_11 h⟩
private noncomputable def tree8 : TapeTree := .split 0 (((58292505395967490732517555116357691162182650861534620031705183625308989491499437192642560000000 : Int) : ℚ)/(denominator : ℚ)) tree9 tree12
attribute [irreducible] tree8
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox8 0 (58292505395967490732517555116357691162182650861534620031705183625308989491499437192642560000000 : Int) false,decode_split denominator ibox8 0 (58292505395967490732517555116357691162182650861534620031705183625308989491499437192642560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_9 h,accepted_12 h⟩
private noncomputable def tree7 : TapeTree := .split 1 (((1258111627251096980211993379540242783045363896706170299175859638815948800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree8 tree19
attribute [irreducible] tree7
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox7 1 (1258111627251096980211993379540242783045363896706170299175859638815948800000000000000000000000 : Int) false,decode_split denominator ibox7 1 (1258111627251096980211993379540242783045363896706170299175859638815948800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_8 h,accepted_19 h⟩
private noncomputable def tree6 : TapeTree := .split 1 (((2516223254502193960423986759080485566090727793412340598351719277631897600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree24
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 1 (2516223254502193960423986759080485566090727793412340598351719277631897600000000000000000000000 : Int) false,decode_split denominator ibox6 1 (2516223254502193960423986759080485566090727793412340598351719277631897600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_7 h,accepted_24 h⟩
private noncomputable def tree5 : TapeTree := .split 1 (((5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree6 tree33
attribute [irreducible] tree5
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox5 1 (5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 : Int) false,decode_split denominator ibox5 1 (5032446509004387920847973518160971132181455586824681196703438555263795200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_6 h,accepted_33 h⟩
private noncomputable def tree4 : TapeTree := .split 1 (((10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree38
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 1 (10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) false,decode_split denominator ibox4 1 (10064893018008775841695947036321942264362911173649362393406877110527590400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_38 h⟩
private noncomputable def tree3 : TapeTree := .split 1 (((20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree43
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 : Int) false,decode_split denominator ibox3 1 (20129786036017551683391894072643884528725822347298724786813754221055180800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_43 h⟩
private noncomputable def tree2 : TapeTree := .split 1 (((40259572072035103366783788145287769057451644694597449573627508442110361600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree48
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 1 (40259572072035103366783788145287769057451644694597449573627508442110361600000000000000000000000 : Int) false,decode_split denominator ibox2 1 (40259572072035103366783788145287769057451644694597449573627508442110361600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_48 h⟩
private noncomputable def tree1 : TapeTree := .face 3 true (candidateRows ibox1) tree2
attribute [irreducible] tree1
private theorem sign_1 : 0 ≤ ((computed denominator ibox1).gradient 3).lo := by decide +kernel
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox1,?_,accepted_2 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox1)).gradient 3).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox1).gradient 3).lo) denominator_positive).2 sign_1
private noncomputable def tree0 : TapeTree := .face 2 true (candidateRows ibox0) tree1
attribute [irreducible] tree0
private theorem sign_0 : 0 ≤ ((computed denominator ibox0).gradient 2).lo := by decide +kernel
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox0,?_,accepted_1 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox0)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox0).gradient 2).lo) denominator_positive).2 sign_0
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (23/32 : ℚ) (3645833333333333/5000000000000000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 56 = e70 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (23/32 : ℚ) (3645833333333333/5000000000000000 : ℚ)) x → eval e70 x ≤ 0 := by
  have hb := h.child_4 tape 56 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell94_high_first_bottom

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell94_high_first_bottom
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((23/32 : ℚ) : ℝ) < p ∧ p ≤ ((3645833333333333/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 94 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 94 p)
    (hkb : ((3645833333333333/5000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((23/32 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ bStar), firstResidual (0 : Fin 9) a p r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell94_high_first_bottom.cell_bound h.child_8 h.child_9 (Cell94_high_first_bottom.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell94_high_first_bottom
