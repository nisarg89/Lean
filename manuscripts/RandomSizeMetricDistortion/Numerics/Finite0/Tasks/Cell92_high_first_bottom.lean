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
namespace Cell92_high_first_bottom
private noncomputable def qValues : Fin 4 → ℚ := ![(9710420744471298587494362428475681157/9432585002715232657537513920099248420 : ℚ),(462757519270084319869750000000000000/471629250135761632876875696004962421 : ℚ),(13323715462055152396315438910280898211/4113956804456539099635847043026444656 : ℚ),(-646571252722648230860312500000000000/257122300278533693727240440189152791 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics20.e2 qValues
private noncomputable abbrev e7 : PolyExpr := SharedFiniteSemantics20.e7 qValues
private noncomputable abbrev e11 : PolyExpr := SharedFiniteSemantics20.e11 qValues
private noncomputable abbrev e15 : PolyExpr := SharedFiniteSemantics20.e15 qValues
private noncomputable abbrev e94 : PolyExpr := SharedFiniteSemantics20.e94 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics20.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics20.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics20.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics20.node_4 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics20.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics20.node_7 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics20.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics20.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics20.node_11 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics20.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics20.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics20.node_15 qValues
private noncomputable abbrev node_53 := SharedFiniteSemantics20.node_53 qValues
private noncomputable abbrev node_54 := SharedFiniteSemantics20.node_54 qValues
private noncomputable abbrev node_55 := SharedFiniteSemantics20.node_55 qValues
private noncomputable abbrev node_56 := SharedFiniteSemantics20.node_56 qValues
private noncomputable abbrev node_57 := SharedFiniteSemantics20.node_57 qValues
private noncomputable abbrev node_58 := SharedFiniteSemantics20.node_58 qValues
private noncomputable abbrev node_59 := SharedFiniteSemantics20.node_59 qValues
private noncomputable abbrev node_60 := SharedFiniteSemantics20.node_60 qValues
private noncomputable abbrev node_61 := SharedFiniteSemantics20.node_61 qValues
private noncomputable abbrev node_62 := SharedFiniteSemantics20.node_62 qValues
private noncomputable abbrev node_63 := SharedFiniteSemantics20.node_63 qValues
private noncomputable abbrev node_65 := SharedFiniteSemantics20.node_65 qValues
private noncomputable abbrev node_66 := SharedFiniteSemantics20.node_66 qValues
private noncomputable abbrev node_67 := SharedFiniteSemantics20.node_67 qValues
private noncomputable abbrev node_72 := SharedFiniteSemantics20.node_72 qValues
private noncomputable abbrev node_73 := SharedFiniteSemantics20.node_73 qValues
private noncomputable abbrev node_74 := SharedFiniteSemantics20.node_74 qValues
private noncomputable abbrev node_75 := SharedFiniteSemantics20.node_75 qValues
private noncomputable abbrev node_76 := SharedFiniteSemantics20.node_76 qValues
private noncomputable abbrev node_93 := SharedFiniteSemantics20.node_93 qValues
private noncomputable abbrev node_94 := SharedFiniteSemantics20.node_94 qValues
private noncomputable abbrev semantic_H_36 := SharedFiniteSemantics20.semantic_H_36 qValues
private noncomputable abbrev semantic_H_52 := SharedFiniteSemantics20.semantic_H_52 qValues
private noncomputable abbrev semantic_psi_92 := SharedFiniteSemantics20.semantic_psi_92 qValues
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
    priceLambda 92 p = ((9710420744471298587494362428475681157/9432585002715232657537513920099248420 : ℝ)+(462757519270084319869750000000000000/471629250135761632876875696004962421 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell92,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 92 p = (((13323715462055152396315438910280898211/4113956804456539099635847043026444656 : ℝ)+(-646571252722648230860312500000000000/257122300278533693727240440189152791 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell92,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e94 x = (x 0*(1-x 0))*(aPoint x+priceLambda 92 (x 0)*(HStar (yPoint x)-HStar (aPoint x))+priceTau 92 (x 0)*psiStar (rPoint x)+(0)-(cStar)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_13,node_14,node_53,node_54,node_55,node_56,node_57,node_58,node_59,node_60,node_61,node_62,node_63,node_65,node_66,node_67,node_72,node_73,node_74,node_75,node_76,node_93,node_94,semantic_H_36,semantic_H_52,semantic_psi_92,point_7,point_11,point_2,point_15]
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
    (hL : lambdaStar (x 0) = priceLambda 92 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 92 (x 0)) :
    (1)*eval e94 x = (x 0*(1-x 0))*(firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (3489583333333333/5000000000000000 : ℚ) (3541666666666667/5000000000000000 : ℚ)) x → eval e94 x ≤ 0)
    (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((3489583333333333/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((3541666666666667/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 92 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 92 p)
    (hkb : ((3541666666666667/5000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((3489583333333333/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ bStar) :
    firstResidual (0 : Fin 9) a p r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨x,hx,hxp,hxa,hxr⟩ := h4 (3489583333333333/5000000000000000 : ℚ) (3541666666666667/5000000000000000 : ℚ) bStar p a r hpcell hkb hr ha hap hcase
  have hcut : ¬(((3541666666666667/5000000000000000 : ℚ) : ℝ) ≤ bStar) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,if_neg hcut] using hxa
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,if_neg hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 92 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 92 (x 0) := by simpa only [hxp] using hT
  have hflag : aPoint x ≤ bStar := by simpa only [hax] using hcase
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e94 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
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
.mul 4 2,
.const (2159811/5000000 : ℚ),
.mul 6 3,
.add 4 7,
.neg 1,
.add 0 9,
.add 5 10,
.const (1085/4818 : ℚ),
.mul 12 11,
.mul 11 11,
.const (19/146 : ℚ),
.mul 15 14,
.mul 11 14,
.const (35/438 : ℚ),
.mul 18 17,
.add 16 19,
.mul 14 14,
.mul 21 21,
.mul 22 22,
.mul 23 23,
.mul 11 24,
.const (1/66 : ℚ),
.mul 26 25,
.add 20 27,
.neg 28,
.add 13 29,
.const (4818/3733 : ℚ),
.mul 31 30,
.mul 12 5,
.mul 5 5,
.mul 15 34,
.mul 5 34,
.mul 18 36,
.add 35 37,
.mul 34 34,
.mul 39 39,
.mul 40 40,
.mul 41 41,
.mul 5 42,
.mul 26 43,
.add 38 44,
.neg 45,
.add 33 46,
.mul 31 47,
.neg 48,
.add 32 49,
.const (9710420744471298587494362428475681157/9432585002715232657537513920099248420 : ℚ),
.const (462757519270084319869750000000000000/471629250135761632876875696004962421 : ℚ),
.mul 52 1,
.add 51 53,
.const (13323715462055152396315438910280898211/4113956804456539099635847043026444656 : ℚ),
.const (-646571252722648230860312500000000000/257122300278533693727240440189152791 : ℚ),
.mul 56 1,
.add 55 57,
.mul 1 10,
.const (-145513/100000 : ℚ),
.add 58 60,
.mul 61 59,
.const (-113609/200000 : ℚ),
.add 5 63,
.mul 64 59,
.mul 54 50,
.add 65 66,
.const (19/73 : ℚ),
.mul 68 8,
.mul 8 8,
.const (35/146 : ℚ),
.mul 71 70,
.add 69 72,
.mul 70 70,
.mul 74 74,
.mul 75 75,
.mul 76 76,
.const (1/2 : ℚ),
.mul 78 77,
.add 73 79,
.neg 80,
.add 12 81,
.mul 31 82,
.mul 62 83,
.add 67 84]
private noncomputable def ssaQVals : Fin 17 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(2159811/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(9710420744471298587494362428475681157/9432585002715232657537513920099248420 : ℚ),(462757519270084319869750000000000000/471629250135761632876875696004962421 : ℚ),(13323715462055152396315438910280898211/4113956804456539099635847043026444656 : ℚ),(-646571252722648230860312500000000000/257122300278533693727240440189152791 : ℚ),(-145513/100000 : ℚ),(-113609/200000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_cb0f818b95c1891e.p86 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_cb0f818b95c1891e.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 85 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_cb0f818b95c1891e.ssa_matches ssaQVals D B

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
private noncomputable def denominator : Int := 56482268697783511524969360118696910386425410293090644462584328995494496887065290165610086400000000000000000000000
private theorem denominator_positive : 0 < denominator := by decide +kernel
private noncomputable def candidateRows (B : Fin 4 → FixedTape.I) : List TapeBounds :=
  (FixedTape.rowsAux denominator B [] tape).map (FixedTape.decodeRow denominator)
private theorem root_in_range : 85 < tape.length := by decide +kernel
private theorem references_valid : tapeRefsValidAux 0 tape = true := by decide +kernel
private theorem candidate_valid (h : Needs) (B : Fin 4 → FixedTape.I) :
    tapeCheck (FixedTape.decodeBox denominator B) tape (candidateRows B) = true :=
  h.child_10.1 denominator denominator_positive B tape references_valid
private theorem candidate_root (B : Fin 4 → FixedTape.I) :
    (candidateRows B).getD 85 zeroTapeBounds = FixedTape.decodeRow denominator (computed denominator B) := by
  unfold candidateRows
  rw [←decode_zeroRow denominator,List.getD_map,ssa_matches]
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨39419916695328071986316952730606450375902059687258819852817960072062570113475717395115580328980655625994240000000,40008273660929991095671209936311079855008673537399898922691252577851566133959846900273603671019344374005760000000⟩,⟨0,56482268697783511524969360118696910386425410293090644462584328995494496887065290165610086400000000000000000000000⟩,⟨0,56482268697783511524969360118696910386425410293090644462584328995494496887065290165610086400000000000000000000000⟩,⟨0,56482268697783511524969360118696910386425410293090644462584328995494496887065290165610086400000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 2 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 3 true
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 1 28241134348891755762484680059348455193212705146545322231292164497747248443532645082805043200000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 14120567174445877881242340029674227596606352573272661115646082248873624221766322541402521600000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 1 7060283587222938940621170014837113798303176286636330557823041124436812110883161270701260800000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox5 1 3530141793611469470310585007418556899151588143318165278911520562218406055441580635350630400000000000000000000000 false
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 1 1765070896805734735155292503709278449575794071659082639455760281109203027720790317675315200000000000000000000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox7 1 882535448402867367577646251854639224787897035829541319727880140554601513860395158837657600000000000000000000000 false
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox7 1 882535448402867367577646251854639224787897035829541319727880140554601513860395158837657600000000000000000000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox6 1 1765070896805734735155292503709278449575794071659082639455760281109203027720790317675315200000000000000000000000 true
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox10 1 2647606345208602102732938755563917674363691107488623959183640421663804541581185476512972800000000000000000000000 false
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox10 1 2647606345208602102732938755563917674363691107488623959183640421663804541581185476512972800000000000000000000000 true
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox5 1 3530141793611469470310585007418556899151588143318165278911520562218406055441580635350630400000000000000000000000 true
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox13 1 5295212690417204205465877511127835348727382214977247918367280843327609083162370953025945600000000000000000000000 false
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox13 1 5295212690417204205465877511127835348727382214977247918367280843327609083162370953025945600000000000000000000000 true
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox4 1 7060283587222938940621170014837113798303176286636330557823041124436812110883161270701260800000000000000000000000 true
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 1 10590425380834408410931755022255670697454764429954495836734561686655218166324741906051891200000000000000000000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox16 1 10590425380834408410931755022255670697454764429954495836734561686655218166324741906051891200000000000000000000000 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox3 1 14120567174445877881242340029674227596606352573272661115646082248873624221766322541402521600000000000000000000000 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 1 21180850761668816821863510044511341394909528859908991673469123373310436332649483812103782400000000000000000000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox19 1 21180850761668816821863510044511341394909528859908991673469123373310436332649483812103782400000000000000000000000 true
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox2 1 28241134348891755762484680059348455193212705146545322231292164497747248443532645082805043200000000000000000000000 true
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox22 1 42361701523337633643727020089022682789819057719817983346938246746620872665298967624207564800000000000000000000000 false
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox22 1 42361701523337633643727020089022682789819057719817983346938246746620872665298967624207564800000000000000000000000 true
private noncomputable def tree24 : TapeTree := .centered (candidateRows ibox24) (candidateRows (FixedTape.midBox ibox24))
attribute [irreducible] tree24
private theorem sign_24 : 2*denominator*(computed denominator (FixedTape.midBox ibox24)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox24).gradient k).lo.natAbs ((computed denominator ibox24).gradient k).hi.natAbs : Int)*((ibox24 k).hi-(ibox24 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox24
    (computed denominator ibox24) (computed denominator (FixedTape.midBox ibox24))
    (by decide +kernel)
private theorem midpoint_even_24 : ∀ k, 2 ∣ (ibox24 k).lo+(ibox24 k).hi := by decide +kernel
private theorem accepted_24 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox24) tree24 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox24 midpoint_even_24
  simp only [tree24,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox24,candidate_valid h (FixedTape.midBox ibox24),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox24 85 (FixedTape.rowsAux denominator ibox24 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox24) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_24
private noncomputable def tree23 : TapeTree := .centered (candidateRows ibox23) (candidateRows (FixedTape.midBox ibox23))
attribute [irreducible] tree23
private theorem sign_23 : 2*denominator*(computed denominator (FixedTape.midBox ibox23)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox23).gradient k).lo.natAbs ((computed denominator ibox23).gradient k).hi.natAbs : Int)*((ibox23 k).hi-(ibox23 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox23
    (computed denominator ibox23) (computed denominator (FixedTape.midBox ibox23))
    (by decide +kernel)
private theorem midpoint_even_23 : ∀ k, 2 ∣ (ibox23 k).lo+(ibox23 k).hi := by decide +kernel
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox23 midpoint_even_23
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox23,candidate_valid h (FixedTape.midBox ibox23),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox23 85 (FixedTape.rowsAux denominator ibox23 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox23) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_23
private noncomputable def tree22 : TapeTree := .split 1 (((42361701523337633643727020089022682789819057719817983346938246746620872665298967624207564800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree23 tree24
attribute [irreducible] tree22
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox22 1 (42361701523337633643727020089022682789819057719817983346938246746620872665298967624207564800000000000000000000000 : Int) false,decode_split denominator ibox22 1 (42361701523337633643727020089022682789819057719817983346938246746620872665298967624207564800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_23 h,accepted_24 h⟩
private noncomputable def tree21 : TapeTree := .centered (candidateRows ibox21) (candidateRows (FixedTape.midBox ibox21))
attribute [irreducible] tree21
private theorem sign_21 : 2*denominator*(computed denominator (FixedTape.midBox ibox21)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox21).gradient k).lo.natAbs ((computed denominator ibox21).gradient k).hi.natAbs : Int)*((ibox21 k).hi-(ibox21 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox21
    (computed denominator ibox21) (computed denominator (FixedTape.midBox ibox21))
    (by decide +kernel)
private theorem midpoint_even_21 : ∀ k, 2 ∣ (ibox21 k).lo+(ibox21 k).hi := by decide +kernel
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox21 midpoint_even_21
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox21,candidate_valid h (FixedTape.midBox ibox21),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox21 85 (FixedTape.rowsAux denominator ibox21 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox21) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_21
private noncomputable def tree20 : TapeTree := .centered (candidateRows ibox20) (candidateRows (FixedTape.midBox ibox20))
attribute [irreducible] tree20
private theorem sign_20 : 2*denominator*(computed denominator (FixedTape.midBox ibox20)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox20).gradient k).lo.natAbs ((computed denominator ibox20).gradient k).hi.natAbs : Int)*((ibox20 k).hi-(ibox20 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox20
    (computed denominator ibox20) (computed denominator (FixedTape.midBox ibox20))
    (by decide +kernel)
private theorem midpoint_even_20 : ∀ k, 2 ∣ (ibox20 k).lo+(ibox20 k).hi := by decide +kernel
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox20 midpoint_even_20
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox20,candidate_valid h (FixedTape.midBox ibox20),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox20 85 (FixedTape.rowsAux denominator ibox20 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox20) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_20
private noncomputable def tree19 : TapeTree := .split 1 (((21180850761668816821863510044511341394909528859908991673469123373310436332649483812103782400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree21
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 1 (21180850761668816821863510044511341394909528859908991673469123373310436332649483812103782400000000000000000000000 : Int) false,decode_split denominator ibox19 1 (21180850761668816821863510044511341394909528859908991673469123373310436332649483812103782400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_20 h,accepted_21 h⟩
private noncomputable def tree18 : TapeTree := .centered (candidateRows ibox18) (candidateRows (FixedTape.midBox ibox18))
attribute [irreducible] tree18
private theorem sign_18 : 2*denominator*(computed denominator (FixedTape.midBox ibox18)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox18).gradient k).lo.natAbs ((computed denominator ibox18).gradient k).hi.natAbs : Int)*((ibox18 k).hi-(ibox18 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox18
    (computed denominator ibox18) (computed denominator (FixedTape.midBox ibox18))
    (by decide +kernel)
private theorem midpoint_even_18 : ∀ k, 2 ∣ (ibox18 k).lo+(ibox18 k).hi := by decide +kernel
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox18 midpoint_even_18
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox18,candidate_valid h (FixedTape.midBox ibox18),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox18 85 (FixedTape.rowsAux denominator ibox18 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox18) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_18
private noncomputable def tree17 : TapeTree := .centered (candidateRows ibox17) (candidateRows (FixedTape.midBox ibox17))
attribute [irreducible] tree17
private theorem sign_17 : 2*denominator*(computed denominator (FixedTape.midBox ibox17)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox17).gradient k).lo.natAbs ((computed denominator ibox17).gradient k).hi.natAbs : Int)*((ibox17 k).hi-(ibox17 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox17
    (computed denominator ibox17) (computed denominator (FixedTape.midBox ibox17))
    (by decide +kernel)
private theorem midpoint_even_17 : ∀ k, 2 ∣ (ibox17 k).lo+(ibox17 k).hi := by decide +kernel
private theorem accepted_17 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox17) tree17 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox17 midpoint_even_17
  simp only [tree17,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox17,candidate_valid h (FixedTape.midBox ibox17),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox17 85 (FixedTape.rowsAux denominator ibox17 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox17) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_17
private noncomputable def tree16 : TapeTree := .split 1 (((10590425380834408410931755022255670697454764429954495836734561686655218166324741906051891200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree18
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 1 (10590425380834408410931755022255670697454764429954495836734561686655218166324741906051891200000000000000000000000 : Int) false,decode_split denominator ibox16 1 (10590425380834408410931755022255670697454764429954495836734561686655218166324741906051891200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_17 h,accepted_18 h⟩
private noncomputable def tree15 : TapeTree := .centered (candidateRows ibox15) (candidateRows (FixedTape.midBox ibox15))
attribute [irreducible] tree15
private theorem sign_15 : 2*denominator*(computed denominator (FixedTape.midBox ibox15)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox15).gradient k).lo.natAbs ((computed denominator ibox15).gradient k).hi.natAbs : Int)*((ibox15 k).hi-(ibox15 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox15
    (computed denominator ibox15) (computed denominator (FixedTape.midBox ibox15))
    (by decide +kernel)
private theorem midpoint_even_15 : ∀ k, 2 ∣ (ibox15 k).lo+(ibox15 k).hi := by decide +kernel
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox15 midpoint_even_15
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox15,candidate_valid h (FixedTape.midBox ibox15),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox15 85 (FixedTape.rowsAux denominator ibox15 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox15) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_15
private noncomputable def tree14 : TapeTree := .centered (candidateRows ibox14) (candidateRows (FixedTape.midBox ibox14))
attribute [irreducible] tree14
private theorem sign_14 : 2*denominator*(computed denominator (FixedTape.midBox ibox14)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox14).gradient k).lo.natAbs ((computed denominator ibox14).gradient k).hi.natAbs : Int)*((ibox14 k).hi-(ibox14 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox14
    (computed denominator ibox14) (computed denominator (FixedTape.midBox ibox14))
    (by decide +kernel)
private theorem midpoint_even_14 : ∀ k, 2 ∣ (ibox14 k).lo+(ibox14 k).hi := by decide +kernel
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox14 midpoint_even_14
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox14,candidate_valid h (FixedTape.midBox ibox14),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox14 85 (FixedTape.rowsAux denominator ibox14 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox14) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_14
private noncomputable def tree13 : TapeTree := .split 1 (((5295212690417204205465877511127835348727382214977247918367280843327609083162370953025945600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree14 tree15
attribute [irreducible] tree13
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox13 1 (5295212690417204205465877511127835348727382214977247918367280843327609083162370953025945600000000000000000000000 : Int) false,decode_split denominator ibox13 1 (5295212690417204205465877511127835348727382214977247918367280843327609083162370953025945600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_14 h,accepted_15 h⟩
private noncomputable def tree12 : TapeTree := .centered (candidateRows ibox12) (candidateRows (FixedTape.midBox ibox12))
attribute [irreducible] tree12
private theorem sign_12 : 2*denominator*(computed denominator (FixedTape.midBox ibox12)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox12).gradient k).lo.natAbs ((computed denominator ibox12).gradient k).hi.natAbs : Int)*((ibox12 k).hi-(ibox12 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox12
    (computed denominator ibox12) (computed denominator (FixedTape.midBox ibox12))
    (by decide +kernel)
private theorem midpoint_even_12 : ∀ k, 2 ∣ (ibox12 k).lo+(ibox12 k).hi := by decide +kernel
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox12 midpoint_even_12
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox12,candidate_valid h (FixedTape.midBox ibox12),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox12 85 (FixedTape.rowsAux denominator ibox12 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox12) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_12
private noncomputable def tree11 : TapeTree := .centered (candidateRows ibox11) (candidateRows (FixedTape.midBox ibox11))
attribute [irreducible] tree11
private theorem sign_11 : 2*denominator*(computed denominator (FixedTape.midBox ibox11)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox11).gradient k).lo.natAbs ((computed denominator ibox11).gradient k).hi.natAbs : Int)*((ibox11 k).hi-(ibox11 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox11
    (computed denominator ibox11) (computed denominator (FixedTape.midBox ibox11))
    (by decide +kernel)
private theorem midpoint_even_11 : ∀ k, 2 ∣ (ibox11 k).lo+(ibox11 k).hi := by decide +kernel
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox11 midpoint_even_11
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox11,candidate_valid h (FixedTape.midBox ibox11),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox11 85 (FixedTape.rowsAux denominator ibox11 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox11) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_11
private noncomputable def tree10 : TapeTree := .split 1 (((2647606345208602102732938755563917674363691107488623959183640421663804541581185476512972800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree11 tree12
attribute [irreducible] tree10
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox10 1 (2647606345208602102732938755563917674363691107488623959183640421663804541581185476512972800000000000000000000000 : Int) false,decode_split denominator ibox10 1 (2647606345208602102732938755563917674363691107488623959183640421663804541581185476512972800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_11 h,accepted_12 h⟩
private noncomputable def tree9 : TapeTree := .centered (candidateRows ibox9) (candidateRows (FixedTape.midBox ibox9))
attribute [irreducible] tree9
private theorem sign_9 : 2*denominator*(computed denominator (FixedTape.midBox ibox9)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox9).gradient k).lo.natAbs ((computed denominator ibox9).gradient k).hi.natAbs : Int)*((ibox9 k).hi-(ibox9 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox9
    (computed denominator ibox9) (computed denominator (FixedTape.midBox ibox9))
    (by decide +kernel)
private theorem midpoint_even_9 : ∀ k, 2 ∣ (ibox9 k).lo+(ibox9 k).hi := by decide +kernel
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox9 midpoint_even_9
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox9,candidate_valid h (FixedTape.midBox ibox9),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox9 85 (FixedTape.rowsAux denominator ibox9 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox9) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_9
private noncomputable def tree8 : TapeTree := .centered (candidateRows ibox8) (candidateRows (FixedTape.midBox ibox8))
attribute [irreducible] tree8
private theorem sign_8 : 2*denominator*(computed denominator (FixedTape.midBox ibox8)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox8).gradient k).lo.natAbs ((computed denominator ibox8).gradient k).hi.natAbs : Int)*((ibox8 k).hi-(ibox8 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox8
    (computed denominator ibox8) (computed denominator (FixedTape.midBox ibox8))
    (by decide +kernel)
private theorem midpoint_even_8 : ∀ k, 2 ∣ (ibox8 k).lo+(ibox8 k).hi := by decide +kernel
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox8 midpoint_even_8
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox8,candidate_valid h (FixedTape.midBox ibox8),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox8 85 (FixedTape.rowsAux denominator ibox8 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox8) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_8
private noncomputable def tree7 : TapeTree := .split 1 (((882535448402867367577646251854639224787897035829541319727880140554601513860395158837657600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree8 tree9
attribute [irreducible] tree7
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox7 1 (882535448402867367577646251854639224787897035829541319727880140554601513860395158837657600000000000000000000000 : Int) false,decode_split denominator ibox7 1 (882535448402867367577646251854639224787897035829541319727880140554601513860395158837657600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_8 h,accepted_9 h⟩
private noncomputable def tree6 : TapeTree := .split 1 (((1765070896805734735155292503709278449575794071659082639455760281109203027720790317675315200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree10
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 1 (1765070896805734735155292503709278449575794071659082639455760281109203027720790317675315200000000000000000000000 : Int) false,decode_split denominator ibox6 1 (1765070896805734735155292503709278449575794071659082639455760281109203027720790317675315200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_7 h,accepted_10 h⟩
private noncomputable def tree5 : TapeTree := .split 1 (((3530141793611469470310585007418556899151588143318165278911520562218406055441580635350630400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree6 tree13
attribute [irreducible] tree5
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox5 1 (3530141793611469470310585007418556899151588143318165278911520562218406055441580635350630400000000000000000000000 : Int) false,decode_split denominator ibox5 1 (3530141793611469470310585007418556899151588143318165278911520562218406055441580635350630400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_6 h,accepted_13 h⟩
private noncomputable def tree4 : TapeTree := .split 1 (((7060283587222938940621170014837113798303176286636330557823041124436812110883161270701260800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree16
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 1 (7060283587222938940621170014837113798303176286636330557823041124436812110883161270701260800000000000000000000000 : Int) false,decode_split denominator ibox4 1 (7060283587222938940621170014837113798303176286636330557823041124436812110883161270701260800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_16 h⟩
private noncomputable def tree3 : TapeTree := .split 1 (((14120567174445877881242340029674227596606352573272661115646082248873624221766322541402521600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree19
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (14120567174445877881242340029674227596606352573272661115646082248873624221766322541402521600000000000000000000000 : Int) false,decode_split denominator ibox3 1 (14120567174445877881242340029674227596606352573272661115646082248873624221766322541402521600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_19 h⟩
private noncomputable def tree2 : TapeTree := .split 1 (((28241134348891755762484680059348455193212705146545322231292164497747248443532645082805043200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree22
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 1 (28241134348891755762484680059348455193212705146545322231292164497747248443532645082805043200000000000000000000000 : Int) false,decode_split denominator ibox2 1 (28241134348891755762484680059348455193212705146545322231292164497747248443532645082805043200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_22 h⟩
private noncomputable def tree1 : TapeTree := .face 3 true (candidateRows ibox1) tree2
attribute [irreducible] tree1
private theorem sign_1 : 0 ≤ ((computed denominator ibox1).gradient 3).lo := by decide +kernel
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox1,?_,accepted_2 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox1)).gradient 3).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox1).gradient 3).lo) denominator_positive).2 sign_1
private noncomputable def tree0 : TapeTree := .face 2 false (candidateRows ibox0) tree1
attribute [irreducible] tree0
private theorem sign_0 : ((computed denominator ibox0).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox0,?_,accepted_1 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox0)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox0).gradient 2).hi) denominator_positive).1 sign_0
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (3489583333333333/5000000000000000 : ℚ) (3541666666666667/5000000000000000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 85 = e94 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (3489583333333333/5000000000000000 : ℚ) (3541666666666667/5000000000000000 : ℚ)) x → eval e94 x ≤ 0 := by
  have hb := h.child_4 tape 85 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell92_high_first_bottom

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell92_high_first_bottom
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((3489583333333333/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((3541666666666667/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 92 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 92 p)
    (hkb : ((3541666666666667/5000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((3489583333333333/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ bStar), firstResidual (0 : Fin 9) a p r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell92_high_first_bottom.cell_bound h.child_8 h.child_9 (Cell92_high_first_bottom.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell92_high_first_bottom
