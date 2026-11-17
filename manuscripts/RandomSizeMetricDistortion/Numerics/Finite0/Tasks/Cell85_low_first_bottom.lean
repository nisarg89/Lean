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
namespace Cell85_low_first_bottom
private noncomputable def qValues : Fin 4 → ℚ := ![(607873604264055574939380066145417159/842437469453025821401758000600236790 : ℚ),(121356033086929406772875000000000000/84243746945302582140175800060023679 : ℚ),(346661780929022179496412421546319879/116460116166449513509220655088713705 : ℚ),(-49458851224383325378000000000000000/23292023233289902701844131017742741 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics16.e2 qValues
private noncomputable abbrev e7 : PolyExpr := SharedFiniteSemantics16.e7 qValues
private noncomputable abbrev e12 : PolyExpr := SharedFiniteSemantics16.e12 qValues
private noncomputable abbrev e16 : PolyExpr := SharedFiniteSemantics16.e16 qValues
private noncomputable abbrev e95 : PolyExpr := SharedFiniteSemantics16.e95 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics16.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics16.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics16.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics16.node_4 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics16.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics16.node_7 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics16.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics16.node_11 qValues
private noncomputable abbrev node_12 := SharedFiniteSemantics16.node_12 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics16.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics16.node_15 qValues
private noncomputable abbrev node_16 := SharedFiniteSemantics16.node_16 qValues
private noncomputable abbrev node_54 := SharedFiniteSemantics16.node_54 qValues
private noncomputable abbrev node_55 := SharedFiniteSemantics16.node_55 qValues
private noncomputable abbrev node_56 := SharedFiniteSemantics16.node_56 qValues
private noncomputable abbrev node_57 := SharedFiniteSemantics16.node_57 qValues
private noncomputable abbrev node_58 := SharedFiniteSemantics16.node_58 qValues
private noncomputable abbrev node_59 := SharedFiniteSemantics16.node_59 qValues
private noncomputable abbrev node_60 := SharedFiniteSemantics16.node_60 qValues
private noncomputable abbrev node_61 := SharedFiniteSemantics16.node_61 qValues
private noncomputable abbrev node_62 := SharedFiniteSemantics16.node_62 qValues
private noncomputable abbrev node_63 := SharedFiniteSemantics16.node_63 qValues
private noncomputable abbrev node_64 := SharedFiniteSemantics16.node_64 qValues
private noncomputable abbrev node_66 := SharedFiniteSemantics16.node_66 qValues
private noncomputable abbrev node_67 := SharedFiniteSemantics16.node_67 qValues
private noncomputable abbrev node_68 := SharedFiniteSemantics16.node_68 qValues
private noncomputable abbrev node_73 := SharedFiniteSemantics16.node_73 qValues
private noncomputable abbrev node_74 := SharedFiniteSemantics16.node_74 qValues
private noncomputable abbrev node_75 := SharedFiniteSemantics16.node_75 qValues
private noncomputable abbrev node_76 := SharedFiniteSemantics16.node_76 qValues
private noncomputable abbrev node_77 := SharedFiniteSemantics16.node_77 qValues
private noncomputable abbrev node_94 := SharedFiniteSemantics16.node_94 qValues
private noncomputable abbrev node_95 := SharedFiniteSemantics16.node_95 qValues
private noncomputable abbrev semantic_H_37 := SharedFiniteSemantics16.semantic_H_37 qValues
private noncomputable abbrev semantic_H_53 := SharedFiniteSemantics16.semantic_H_53 qValues
private noncomputable abbrev semantic_psi_93 := SharedFiniteSemantics16.semantic_psi_93 qValues
private noncomputable def aPoint (x : Fin 4 → ℝ) : ℝ := ((49/100 : ℚ) : ℝ)*x 1
private noncomputable def rPoint (x : Fin 4 → ℝ) : ℝ := ((49/100 : ℚ) : ℝ)+(((2840189/5000000 : ℚ) : ℝ)-((49/100 : ℚ) : ℝ))*x 2
private noncomputable def yPoint (x : Fin 4 → ℝ) : ℝ := aPoint x+1-x 0
private theorem point_7 (x : Fin 4 → ℝ) : eval e7 x = aPoint x := by
  simp only [node_3,node_6,node_7] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_12 (x : Fin 4 → ℝ) : eval e12 x = rPoint x := by
  simp only [node_4,node_6,node_10,node_11,node_12] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_2 (x : Fin 4 → ℝ) : eval e2 x = x 0 := by
  simp only [node_2] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_16 (x : Fin 4 → ℝ) : eval e16 x = yPoint x := by
  simp only [node_1,node_2,node_3,node_6,node_7,node_14,node_15,node_16] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem price_lambda_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceLambda 85 p = ((607873604264055574939380066145417159/842437469453025821401758000600236790 : ℝ)+(121356033086929406772875000000000000/84243746945302582140175800060023679 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell85,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 85 p = (((346661780929022179496412421546319879/116460116166449513509220655088713705 : ℝ)+(-49458851224383325378000000000000000/23292023233289902701844131017742741 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell85,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e95 x = (x 0*(1-x 0))*(aPoint x+priceLambda 85 (x 0)*(HStar (yPoint x)-HStar (aPoint x))+priceTau 85 (x 0)*psiStar (rPoint x)+(0)-(cStar)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_14,node_15,node_54,node_55,node_56,node_57,node_58,node_59,node_60,node_61,node_62,node_63,node_64,node_66,node_67,node_68,node_73,node_74,node_75,node_76,node_77,node_94,node_95,semantic_H_37,semantic_H_53,semantic_psi_93,point_7,point_12,point_2,point_16]
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
    (hL : lambdaStar (x 0) = priceLambda 85 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 85 (x 0)) :
    (1)*eval e95 x = (x 0*(1-x 0))*(firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (5/8 : ℚ) (3177083333333333/5000000000000000 : ℚ)) x → eval e95 x ≤ 0)
    (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((5/8 : ℚ) : ℝ) < p ∧ p ≤ ((3177083333333333/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 85 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 85 p)
    (hk0 : ((3177083333333333/5000000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((5/8 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ ((49/100 : ℚ) : ℝ)) :
    firstResidual (0 : Fin 9) a p r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨x,hx,hxp,hxa,hxr⟩ := h1 (5/8 : ℚ) (3177083333333333/5000000000000000 : ℚ) ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ) p a r hpcell hk0 hr ha hap hcase
  have hcut : ¬(((3177083333333333/5000000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ)) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,if_neg hcut] using hxa
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,if_neg hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 85 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 85 (x 0) := by simpa only [hxp] using hT
  have hrootb : ((2840189/5000000 : ℚ) : ℝ) ≤ bStar := by norm_num [bStar]
  have hflag : aPoint x ≤ bStar := by rw [hax]; exact (hap.trans (min_le_right _ _)).trans (hr.2.trans hrootb)
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e95 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
  rw [actual_identity hs x hpx hflag hLx hTx] at hv
  have hscale : 0 < x 0*(1-x 0) := mul_pos hpx.1 (sub_pos.mpr hpx.2)
  have hv : firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x) ≤ 0 := le_of_not_gt (fun hpos => (not_lt_of_ge hv) (mul_pos hscale hpos))
  simpa only [hxp,hax,hrx] using hv
private noncomputable def tape : List TapeOp := [
.const (1/1 : ℚ),
.var 0,
.var 1,
.var 2,
.const (49/100 : ℚ),
.mul 4 2,
.const (390189/5000000 : ℚ),
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
.const (607873604264055574939380066145417159/842437469453025821401758000600236790 : ℚ),
.const (121356033086929406772875000000000000/84243746945302582140175800060023679 : ℚ),
.mul 52 1,
.add 51 53,
.const (346661780929022179496412421546319879/116460116166449513509220655088713705 : ℚ),
.const (-49458851224383325378000000000000000/23292023233289902701844131017742741 : ℚ),
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
private noncomputable def ssaQVals : Fin 17 → ℚ := ![(1/1 : ℚ),(49/100 : ℚ),(390189/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(607873604264055574939380066145417159/842437469453025821401758000600236790 : ℚ),(121356033086929406772875000000000000/84243746945302582140175800060023679 : ℚ),(346661780929022179496412421546319879/116460116166449513509220655088713705 : ℚ),(-49458851224383325378000000000000000/23292023233289902701844131017742741 : ℚ),(-145513/100000 : ℚ),(-113609/200000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
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
private noncomputable def denominator : Int := 4026352101756397349551948873488531189245133295785717574952402747977815055309357323628471910400000000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨2516470063597748343469968045930331993278208309866073484345251717486134409568348327267794944000000000000000000000000,2558411231324377214104327396269347556369586882461762092742119527063064986234304267534587839109511758101872640000000⟩,⟨0,4026352101756397349551948873488531189245133295785717574952402747977815055309357323628471910400000000000000000000000⟩,⟨0,4026352101756397349551948873488531189245133295785717574952402747977815055309357323628471910400000000000000000000000⟩,⟨0,4026352101756397349551948873488531189245133295785717574952402747977815055309357323628471910400000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 2 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 3 true
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 1 2013176050878198674775974436744265594622566647892858787476201373988907527654678661814235955200000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 1006588025439099337387987218372132797311283323946429393738100686994453763827339330907117977600000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 1 503294012719549668693993609186066398655641661973214696869050343497226881913669665453558988800000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox5 1 251647006359774834346996804593033199327820830986607348434525171748613440956834832726779494400000000000000000000000 false
private noncomputable def ibox7 : Fin 4 → FixedTape.I := faceI ibox6 1 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox5 1 251647006359774834346996804593033199327820830986607348434525171748613440956834832726779494400000000000000000000000 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox4 1 503294012719549668693993609186066398655641661973214696869050343497226881913669665453558988800000000000000000000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox3 1 1006588025439099337387987218372132797311283323946429393738100686994453763827339330907117977600000000000000000000000 true
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox10 1 1509882038158649006081980827558199195966924985919644090607151030491680645741008996360676966400000000000000000000000 false
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox10 1 1509882038158649006081980827558199195966924985919644090607151030491680645741008996360676966400000000000000000000000 true
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox2 1 2013176050878198674775974436744265594622566647892858787476201373988907527654678661814235955200000000000000000000000 true
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox13 1 3019764076317298012163961655116398391933849971839288181214302060983361291482017992721353932800000000000000000000000 false
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox13 1 3019764076317298012163961655116398391933849971839288181214302060983361291482017992721353932800000000000000000000000 true
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
private noncomputable def tree13 : TapeTree := .split 1 (((3019764076317298012163961655116398391933849971839288181214302060983361291482017992721353932800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree14 tree15
attribute [irreducible] tree13
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox13 1 (3019764076317298012163961655116398391933849971839288181214302060983361291482017992721353932800000000000000000000000 : Int) false,decode_split denominator ibox13 1 (3019764076317298012163961655116398391933849971839288181214302060983361291482017992721353932800000000000000000000000 : Int) true]
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
private noncomputable def tree10 : TapeTree := .split 1 (((1509882038158649006081980827558199195966924985919644090607151030491680645741008996360676966400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree11 tree12
attribute [irreducible] tree10
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox10 1 (1509882038158649006081980827558199195966924985919644090607151030491680645741008996360676966400000000000000000000000 : Int) false,decode_split denominator ibox10 1 (1509882038158649006081980827558199195966924985919644090607151030491680645741008996360676966400000000000000000000000 : Int) true]
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
private noncomputable def tree7 : TapeTree := .centered (candidateRows ibox7) (candidateRows (FixedTape.midBox ibox7))
attribute [irreducible] tree7
private theorem sign_7 : 2*denominator*(computed denominator (FixedTape.midBox ibox7)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox7).gradient k).lo.natAbs ((computed denominator ibox7).gradient k).hi.natAbs : Int)*((ibox7 k).hi-(ibox7 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox7
    (computed denominator ibox7) (computed denominator (FixedTape.midBox ibox7))
    (by decide +kernel)
private theorem midpoint_even_7 : ∀ k, 2 ∣ (ibox7 k).lo+(ibox7 k).hi := by decide +kernel
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox7 midpoint_even_7
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox7,candidate_valid h (FixedTape.midBox ibox7),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox7 85 (FixedTape.rowsAux denominator ibox7 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox7) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_7
private noncomputable def tree6 : TapeTree := .face 1 false (candidateRows ibox6) tree7
attribute [irreducible] tree6
private theorem sign_6 : ((computed denominator ibox6).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox6,?_,accepted_7 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox6)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox6).gradient 1).hi) denominator_positive).1 sign_6
private noncomputable def tree5 : TapeTree := .split 1 (((251647006359774834346996804593033199327820830986607348434525171748613440956834832726779494400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree6 tree8
attribute [irreducible] tree5
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox5 1 (251647006359774834346996804593033199327820830986607348434525171748613440956834832726779494400000000000000000000000 : Int) false,decode_split denominator ibox5 1 (251647006359774834346996804593033199327820830986607348434525171748613440956834832726779494400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_6 h,accepted_8 h⟩
private noncomputable def tree4 : TapeTree := .split 1 (((503294012719549668693993609186066398655641661973214696869050343497226881913669665453558988800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree9
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 1 (503294012719549668693993609186066398655641661973214696869050343497226881913669665453558988800000000000000000000000 : Int) false,decode_split denominator ibox4 1 (503294012719549668693993609186066398655641661973214696869050343497226881913669665453558988800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_9 h⟩
private noncomputable def tree3 : TapeTree := .split 1 (((1006588025439099337387987218372132797311283323946429393738100686994453763827339330907117977600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree10
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (1006588025439099337387987218372132797311283323946429393738100686994453763827339330907117977600000000000000000000000 : Int) false,decode_split denominator ibox3 1 (1006588025439099337387987218372132797311283323946429393738100686994453763827339330907117977600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_10 h⟩
private noncomputable def tree2 : TapeTree := .split 1 (((2013176050878198674775974436744265594622566647892858787476201373988907527654678661814235955200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree13
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 1 (2013176050878198674775974436744265594622566647892858787476201373988907527654678661814235955200000000000000000000000 : Int) false,decode_split denominator ibox2 1 (2013176050878198674775974436744265594622566647892858787476201373988907527654678661814235955200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_13 h⟩
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
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (5/8 : ℚ) (3177083333333333/5000000000000000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 85 = e95 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (5/8 : ℚ) (3177083333333333/5000000000000000 : ℚ)) x → eval e95 x ≤ 0 := by
  have hb := h.child_4 tape 85 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell85_low_first_bottom

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell85_low_first_bottom
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((5/8 : ℚ) : ℝ) < p ∧ p ≤ ((3177083333333333/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 85 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 85 p)
    (hk0 : ((3177083333333333/5000000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((5/8 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ ((49/100 : ℚ) : ℝ)), firstResidual (0 : Fin 9) a p r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell85_low_first_bottom.cell_bound h.child_8 h.child_9 (Cell85_low_first_bottom.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell85_low_first_bottom
