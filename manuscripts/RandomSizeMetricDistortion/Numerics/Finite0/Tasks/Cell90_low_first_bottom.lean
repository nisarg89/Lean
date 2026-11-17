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
namespace Cell90_low_first_bottom
private noncomputable def qValues : Fin 4 → ℚ := ![(7561059334030734048730308975568168568/8242985148892576697193953337171505287 : ℚ),(9422352191074354292075000000000000000/8242985148892576697193953337171505287 : ℚ),(28351259775094450317121001657998573373/9009058626300321467676649316462484717 : ℚ),(-21462397941076195389010000000000000000/9009058626300321467676649316462484717 : ℚ)]
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
    priceLambda 90 p = ((7561059334030734048730308975568168568/8242985148892576697193953337171505287 : ℝ)+(9422352191074354292075000000000000000/8242985148892576697193953337171505287 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell90,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 90 p = (((28351259775094450317121001657998573373/9009058626300321467676649316462484717 : ℝ)+(-21462397941076195389010000000000000000/9009058626300321467676649316462484717 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell90,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e95 x = (x 0*(1-x 0))*(aPoint x+priceLambda 90 (x 0)*(HStar (yPoint x)-HStar (aPoint x))+priceTau 90 (x 0)*psiStar (rPoint x)+(0)-(cStar)) := by
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
    (hL : lambdaStar (x 0) = priceLambda 90 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 90 (x 0)) :
    (1)*eval e95 x = (x 0*(1-x 0))*(firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (3385416666666667/5000000000000000 : ℚ) (11/16 : ℚ)) x → eval e95 x ≤ 0)
    (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((3385416666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((11/16 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 90 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 90 p)
    (hk0 : ((11/16 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((3385416666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ ((49/100 : ℚ) : ℝ)) :
    firstResidual (0 : Fin 9) a p r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨x,hx,hxp,hxa,hxr⟩ := h1 (3385416666666667/5000000000000000 : ℚ) (11/16 : ℚ) ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ) p a r hpcell hk0 hr ha hap hcase
  have hcut : ¬(((11/16 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ)) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,if_neg hcut] using hxa
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,if_neg hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 90 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 90 (x 0) := by simpa only [hxp] using hT
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
.const (7561059334030734048730308975568168568/8242985148892576697193953337171505287 : ℚ),
.const (9422352191074354292075000000000000000/8242985148892576697193953337171505287 : ℚ),
.mul 52 1,
.add 51 53,
.const (28351259775094450317121001657998573373/9009058626300321467676649316462484717 : ℚ),
.const (-21462397941076195389010000000000000000/9009058626300321467676649316462484717 : ℚ),
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
private noncomputable def ssaQVals : Fin 17 → ℚ := ![(1/1 : ℚ),(49/100 : ℚ),(390189/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(7561059334030734048730308975568168568/8242985148892576697193953337171505287 : ℚ),(9422352191074354292075000000000000000/8242985148892576697193953337171505287 : ℚ),(28351259775094450317121001657998573373/9009058626300321467676649316462484717 : ℚ),(-21462397941076195389010000000000000000/9009058626300321467676649316462484717 : ℚ),(-145513/100000 : ℚ),(-113609/200000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
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
private noncomputable def denominator : Int := 1391607218157102478724176890549751170938960491131049458355872827594134990938198837931619332915200000000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨942234053960538229409975980116559270268380535853392800025821635753492790505927302791866652541255862107955527680000000,956729962483007954122871612252953930020535337652596502619662568970967806270011701077988291379200000000000000000000000⟩,⟨0,1391607218157102478724176890549751170938960491131049458355872827594134990938198837931619332915200000000000000000000000⟩,⟨0,1391607218157102478724176890549751170938960491131049458355872827594134990938198837931619332915200000000000000000000000⟩,⟨0,1391607218157102478724176890549751170938960491131049458355872827594134990938198837931619332915200000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 2 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 3 true
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 1 695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 1 173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox5 1 86975451134818904920261055659359448183685030695690591147242051724633436933637427370726208307200000000000000000000000 false
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 1 43487725567409452460130527829679724091842515347845295573621025862316718466818713685363104153600000000000000000000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox7 1 21743862783704726230065263914839862045921257673922647786810512931158359233409356842681552076800000000000000000000000 false
private noncomputable def ibox9 : Fin 4 → FixedTape.I := faceI ibox8 1 false
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox9 0 949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 false
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox9 0 949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox7 1 21743862783704726230065263914839862045921257673922647786810512931158359233409356842681552076800000000000000000000000 true
private noncomputable def ibox13 : Fin 4 → FixedTape.I := faceI ibox12 1 false
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox6 1 43487725567409452460130527829679724091842515347845295573621025862316718466818713685363104153600000000000000000000000 true
private noncomputable def ibox15 : Fin 4 → FixedTape.I := faceI ibox14 1 false
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox5 1 86975451134818904920261055659359448183685030695690591147242051724633436933637427370726208307200000000000000000000000 true
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 1 130463176702228357380391583489039172275527546043535886720863077586950155400456141056089312460800000000000000000000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox16 1 130463176702228357380391583489039172275527546043535886720863077586950155400456141056089312460800000000000000000000000 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox4 1 173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 1 260926353404456714760783166978078344551055092087071773441726155173900310800912282112178624921600000000000000000000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox19 1 260926353404456714760783166978078344551055092087071773441726155173900310800912282112178624921600000000000000000000000 true
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox3 1 347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 true
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox22 1 521852706808913429521566333956156689102110184174143546883452310347800621601824564224357249843200000000000000000000000 false
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox22 1 521852706808913429521566333956156689102110184174143546883452310347800621601824564224357249843200000000000000000000000 true
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox2 1 695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 true
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox25 1 1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 false
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox25 1 1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 true
private noncomputable def tree27 : TapeTree := .centered (candidateRows ibox27) (candidateRows (FixedTape.midBox ibox27))
attribute [irreducible] tree27
private theorem sign_27 : 2*denominator*(computed denominator (FixedTape.midBox ibox27)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox27).gradient k).lo.natAbs ((computed denominator ibox27).gradient k).hi.natAbs : Int)*((ibox27 k).hi-(ibox27 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox27
    (computed denominator ibox27) (computed denominator (FixedTape.midBox ibox27))
    (by decide +kernel)
private theorem midpoint_even_27 : ∀ k, 2 ∣ (ibox27 k).lo+(ibox27 k).hi := by decide +kernel
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox27 midpoint_even_27
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox27,candidate_valid h (FixedTape.midBox ibox27),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox27 85 (FixedTape.rowsAux denominator ibox27 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox27) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_27
private noncomputable def tree26 : TapeTree := .centered (candidateRows ibox26) (candidateRows (FixedTape.midBox ibox26))
attribute [irreducible] tree26
private theorem sign_26 : 2*denominator*(computed denominator (FixedTape.midBox ibox26)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox26).gradient k).lo.natAbs ((computed denominator ibox26).gradient k).hi.natAbs : Int)*((ibox26 k).hi-(ibox26 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox26
    (computed denominator ibox26) (computed denominator (FixedTape.midBox ibox26))
    (by decide +kernel)
private theorem midpoint_even_26 : ∀ k, 2 ∣ (ibox26 k).lo+(ibox26 k).hi := by decide +kernel
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox26 midpoint_even_26
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox26,candidate_valid h (FixedTape.midBox ibox26),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox26 85 (FixedTape.rowsAux denominator ibox26 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox26) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_26
private noncomputable def tree25 : TapeTree := .split 1 (((1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree26 tree27
attribute [irreducible] tree25
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox25 1 (1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) false,decode_split denominator ibox25 1 (1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_26 h,accepted_27 h⟩
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
private noncomputable def tree22 : TapeTree := .split 1 (((521852706808913429521566333956156689102110184174143546883452310347800621601824564224357249843200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree23 tree24
attribute [irreducible] tree22
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox22 1 (521852706808913429521566333956156689102110184174143546883452310347800621601824564224357249843200000000000000000000000 : Int) false,decode_split denominator ibox22 1 (521852706808913429521566333956156689102110184174143546883452310347800621601824564224357249843200000000000000000000000 : Int) true]
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
private noncomputable def tree19 : TapeTree := .split 1 (((260926353404456714760783166978078344551055092087071773441726155173900310800912282112178624921600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree21
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 1 (260926353404456714760783166978078344551055092087071773441726155173900310800912282112178624921600000000000000000000000 : Int) false,decode_split denominator ibox19 1 (260926353404456714760783166978078344551055092087071773441726155173900310800912282112178624921600000000000000000000000 : Int) true]
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
private noncomputable def tree16 : TapeTree := .split 1 (((130463176702228357380391583489039172275527546043535886720863077586950155400456141056089312460800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree18
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 1 (130463176702228357380391583489039172275527546043535886720863077586950155400456141056089312460800000000000000000000000 : Int) false,decode_split denominator ibox16 1 (130463176702228357380391583489039172275527546043535886720863077586950155400456141056089312460800000000000000000000000 : Int) true]
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
private noncomputable def tree14 : TapeTree := .face 1 false (candidateRows ibox14) tree15
attribute [irreducible] tree14
private theorem sign_14 : ((computed denominator ibox14).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox14,?_,accepted_15 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox14)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox14).gradient 1).hi) denominator_positive).1 sign_14
private noncomputable def tree13 : TapeTree := .centered (candidateRows ibox13) (candidateRows (FixedTape.midBox ibox13))
attribute [irreducible] tree13
private theorem sign_13 : 2*denominator*(computed denominator (FixedTape.midBox ibox13)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox13).gradient k).lo.natAbs ((computed denominator ibox13).gradient k).hi.natAbs : Int)*((ibox13 k).hi-(ibox13 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox13
    (computed denominator ibox13) (computed denominator (FixedTape.midBox ibox13))
    (by decide +kernel)
private theorem midpoint_even_13 : ∀ k, 2 ∣ (ibox13 k).lo+(ibox13 k).hi := by decide +kernel
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox13 midpoint_even_13
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox13,candidate_valid h (FixedTape.midBox ibox13),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox13 85 (FixedTape.rowsAux denominator ibox13 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox13) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_13
private noncomputable def tree12 : TapeTree := .face 1 false (candidateRows ibox12) tree13
attribute [irreducible] tree12
private theorem sign_12 : ((computed denominator ibox12).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox12,?_,accepted_13 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox12)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox12).gradient 1).hi) denominator_positive).1 sign_12
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
private noncomputable def tree10 : TapeTree := .centered (candidateRows ibox10) (candidateRows (FixedTape.midBox ibox10))
attribute [irreducible] tree10
private theorem sign_10 : 2*denominator*(computed denominator (FixedTape.midBox ibox10)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox10).gradient k).lo.natAbs ((computed denominator ibox10).gradient k).hi.natAbs : Int)*((ibox10 k).hi-(ibox10 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox10
    (computed denominator ibox10) (computed denominator (FixedTape.midBox ibox10))
    (by decide +kernel)
private theorem midpoint_even_10 : ∀ k, 2 ∣ (ibox10 k).lo+(ibox10 k).hi := by decide +kernel
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox10 midpoint_even_10
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox10,candidate_valid h (FixedTape.midBox ibox10),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox10 85 (FixedTape.rowsAux denominator ibox10 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox10) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_10
private noncomputable def tree9 : TapeTree := .split 0 (((949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) : ℚ)/(denominator : ℚ)) tree10 tree11
attribute [irreducible] tree9
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox9 0 (949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) false,decode_split denominator ibox9 0 (949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_10 h,accepted_11 h⟩
private noncomputable def tree8 : TapeTree := .face 1 false (candidateRows ibox8) tree9
attribute [irreducible] tree8
private theorem sign_8 : ((computed denominator ibox8).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox8,?_,accepted_9 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox8)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox8).gradient 1).hi) denominator_positive).1 sign_8
private noncomputable def tree7 : TapeTree := .split 1 (((21743862783704726230065263914839862045921257673922647786810512931158359233409356842681552076800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree8 tree12
attribute [irreducible] tree7
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox7 1 (21743862783704726230065263914839862045921257673922647786810512931158359233409356842681552076800000000000000000000000 : Int) false,decode_split denominator ibox7 1 (21743862783704726230065263914839862045921257673922647786810512931158359233409356842681552076800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_8 h,accepted_12 h⟩
private noncomputable def tree6 : TapeTree := .split 1 (((43487725567409452460130527829679724091842515347845295573621025862316718466818713685363104153600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree14
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 1 (43487725567409452460130527829679724091842515347845295573621025862316718466818713685363104153600000000000000000000000 : Int) false,decode_split denominator ibox6 1 (43487725567409452460130527829679724091842515347845295573621025862316718466818713685363104153600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_7 h,accepted_14 h⟩
private noncomputable def tree5 : TapeTree := .split 1 (((86975451134818904920261055659359448183685030695690591147242051724633436933637427370726208307200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree6 tree16
attribute [irreducible] tree5
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox5 1 (86975451134818904920261055659359448183685030695690591147242051724633436933637427370726208307200000000000000000000000 : Int) false,decode_split denominator ibox5 1 (86975451134818904920261055659359448183685030695690591147242051724633436933637427370726208307200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_6 h,accepted_16 h⟩
private noncomputable def tree4 : TapeTree := .split 1 (((173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree19
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 1 (173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 : Int) false,decode_split denominator ibox4 1 (173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_19 h⟩
private noncomputable def tree3 : TapeTree := .split 1 (((347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree22
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) false,decode_split denominator ibox3 1 (347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_22 h⟩
private noncomputable def tree2 : TapeTree := .split 1 (((695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree25
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 1 (695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) false,decode_split denominator ibox2 1 (695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_25 h⟩
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
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (3385416666666667/5000000000000000 : ℚ) (11/16 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 85 = e95 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (3385416666666667/5000000000000000 : ℚ) (11/16 : ℚ)) x → eval e95 x ≤ 0 := by
  have hb := h.child_4 tape 85 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell90_low_first_bottom

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell90_low_first_bottom
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((3385416666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((11/16 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 90 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 90 p)
    (hk0 : ((11/16 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((3385416666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ ((49/100 : ℚ) : ℝ)), firstResidual (0 : Fin 9) a p r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell90_low_first_bottom.cell_bound h.child_8 h.child_9 (Cell90_low_first_bottom.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell90_low_first_bottom
