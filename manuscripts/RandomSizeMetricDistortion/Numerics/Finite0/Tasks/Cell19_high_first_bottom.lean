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
namespace Cell19_high_first_bottom
private noncomputable def qValues : Fin 2 → ℚ := ![(4934115939670138825732204861111094943/390625000000000000000000000000000000000 : ℚ),(4219877/800000 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics6.e2 qValues
private noncomputable abbrev e6 : PolyExpr := SharedFiniteSemantics6.e6 qValues
private noncomputable abbrev e11 : PolyExpr := SharedFiniteSemantics6.e11 qValues
private noncomputable abbrev e15 : PolyExpr := SharedFiniteSemantics6.e15 qValues
private noncomputable abbrev e93 : PolyExpr := SharedFiniteSemantics6.e93 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics6.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics6.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics6.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics6.node_4 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics6.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics6.node_7 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics6.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics6.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics6.node_11 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics6.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics6.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics6.node_15 qValues
private noncomputable abbrev node_53 := SharedFiniteSemantics6.node_53 qValues
private noncomputable abbrev node_54 := SharedFiniteSemantics6.node_54 qValues
private noncomputable abbrev node_55 := SharedFiniteSemantics6.node_55 qValues
private noncomputable abbrev node_56 := SharedFiniteSemantics6.node_56 qValues
private noncomputable abbrev node_57 := SharedFiniteSemantics6.node_57 qValues
private noncomputable abbrev node_58 := SharedFiniteSemantics6.node_58 qValues
private noncomputable abbrev node_59 := SharedFiniteSemantics6.node_59 qValues
private noncomputable abbrev node_60 := SharedFiniteSemantics6.node_60 qValues
private noncomputable abbrev node_61 := SharedFiniteSemantics6.node_61 qValues
private noncomputable abbrev node_62 := SharedFiniteSemantics6.node_62 qValues
private noncomputable abbrev node_63 := SharedFiniteSemantics6.node_63 qValues
private noncomputable abbrev node_64 := SharedFiniteSemantics6.node_64 qValues
private noncomputable abbrev node_65 := SharedFiniteSemantics6.node_65 qValues
private noncomputable abbrev node_66 := SharedFiniteSemantics6.node_66 qValues
private noncomputable abbrev node_71 := SharedFiniteSemantics6.node_71 qValues
private noncomputable abbrev node_72 := SharedFiniteSemantics6.node_72 qValues
private noncomputable abbrev node_73 := SharedFiniteSemantics6.node_73 qValues
private noncomputable abbrev node_74 := SharedFiniteSemantics6.node_74 qValues
private noncomputable abbrev node_75 := SharedFiniteSemantics6.node_75 qValues
private noncomputable abbrev node_92 := SharedFiniteSemantics6.node_92 qValues
private noncomputable abbrev node_93 := SharedFiniteSemantics6.node_93 qValues
private noncomputable abbrev semantic_H_36 := SharedFiniteSemantics6.semantic_H_36 qValues
private noncomputable abbrev semantic_H_52 := SharedFiniteSemantics6.semantic_H_52 qValues
private noncomputable abbrev semantic_psi_91 := SharedFiniteSemantics6.semantic_psi_91 qValues
private noncomputable def aPoint (x : Fin 4 → ℝ) : ℝ := x 0*x 1
private noncomputable def rPoint (x : Fin 4 → ℝ) : ℝ := bStar+(1-bStar)*x 2
private noncomputable def yPoint (x : Fin 4 → ℝ) : ℝ := aPoint x+1-x 0
private theorem point_6 (x : Fin 4 → ℝ) : eval e6 x = aPoint x := by
  simp only [node_2,node_3,node_6] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_11 (x : Fin 4 → ℝ) : eval e11 x = rPoint x := by
  simp only [node_4,node_7,node_9,node_10,node_11] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_2 (x : Fin 4 → ℝ) : eval e2 x = x 0 := by
  simp only [node_2] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_15 (x : Fin 4 → ℝ) : eval e15 x = yPoint x := by
  simp only [node_1,node_2,node_3,node_6,node_13,node_14,node_15] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem price_lambda_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceLambda 19 p = ((4934115939670138825732204861111094943/390625000000000000000000000000000000000 : ℝ)+(4219877/800000 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell19,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 19 p = (((145513/100000 : ℝ)+(145513/25000 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell19,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e93 x = (x 0*(1-x 0))*(aPoint x+priceLambda 19 (x 0)*(HStar (yPoint x)-HStar (aPoint x))+priceTau 19 (x 0)*psiStar (rPoint x)+(0)-(cStar)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_13,node_14,node_53,node_54,node_55,node_56,node_57,node_58,node_59,node_60,node_61,node_62,node_63,node_64,node_65,node_66,node_71,node_72,node_73,node_74,node_75,node_92,node_93,semantic_H_36,semantic_H_52,semantic_psi_91,point_6,point_11,point_2,point_15]
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
    (hL : lambdaStar (x 0) = priceLambda 19 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 19 (x 0)) :
    (1)*eval e93 x = (x 0*(1-x 0))*(firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (5208333333333333/125000000000000000 : ℚ) (6510416666666667/125000000000000000 : ℚ)) x → eval e93 x ≤ 0)
    (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((5208333333333333/125000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((6510416666666667/125000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 19 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 19 p)
    (hkb : ((6510416666666667/125000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((5208333333333333/125000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ bStar) :
    firstResidual (0 : Fin 9) a p r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨x,hx,hxp,hxa,hxr⟩ := h4 (5208333333333333/125000000000000000 : ℚ) (6510416666666667/125000000000000000 : ℚ) bStar p a r hpcell hkb hr ha hap hcase
  have hcut : ((6510416666666667/125000000000000000 : ℚ) : ℝ) ≤ bStar := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,if_pos hcut] using hxa
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,if_pos hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 19 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 19 (x 0) := by simpa only [hxp] using hT
  have hflag : aPoint x ≤ bStar := by simpa only [hax] using hcase
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e93 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
  rw [actual_identity hs x hpx hflag hLx hTx] at hv
  have hscale : 0 < x 0*(1-x 0) := mul_pos hpx.1 (sub_pos.mpr hpx.2)
  have hv : firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x) ≤ 0 := le_of_not_gt (fun hpos => (not_lt_of_ge hv) (mul_pos hscale hpos))
  simpa only [hxp,hax,hrx] using hv
private noncomputable def tape : List TapeOp := [
.const (1/1 : ℚ),
.var 0,
.var 1,
.var 2,
.mul 1 2,
.const (2840189/5000000 : ℚ),
.const (2159811/5000000 : ℚ),
.mul 6 3,
.add 5 7,
.neg 1,
.add 0 9,
.add 4 10,
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
.mul 12 4,
.mul 4 4,
.mul 15 34,
.mul 4 34,
.mul 18 36,
.add 35 37,
.mul 34 34,
.mul 39 39,
.mul 40 40,
.mul 41 41,
.mul 4 42,
.mul 26 43,
.add 38 44,
.neg 45,
.add 33 46,
.mul 31 47,
.neg 48,
.add 32 49,
.const (4934115939670138825732204861111094943/390625000000000000000000000000000000000 : ℚ),
.const (4219877/800000 : ℚ),
.mul 52 1,
.add 51 53,
.const (145513/100000 : ℚ),
.const (145513/25000 : ℚ),
.mul 56 1,
.add 55 57,
.mul 1 10,
.const (-145513/100000 : ℚ),
.add 58 60,
.mul 61 59,
.const (-113609/200000 : ℚ),
.add 4 63,
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
private noncomputable def ssaQVals : Fin 17 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(2159811/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(4934115939670138825732204861111094943/390625000000000000000000000000000000000 : ℚ),(4219877/800000 : ℚ),(145513/100000 : ℚ),(145513/25000 : ℚ),(-145513/100000 : ℚ),(-113609/200000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_5c0a572e934b60cd.p86 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_5c0a572e934b60cd.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 85 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_5c0a572e934b60cd.ssa_matches ssaQVals D B

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
private noncomputable def denominator : Int := 34789198348329530874912561325670400000000000000000000000000000000000000000000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨1449549931180397027016827793024184333566503131545600000000000000000000000000000000000000000,1811937413975496492506224831257415666433496868454400000000000000000000000000000000000000000⟩,⟨0,34789198348329530874912561325670400000000000000000000000000000000000000000000000000000000000⟩,⟨0,34789198348329530874912561325670400000000000000000000000000000000000000000000000000000000000⟩,⟨0,34789198348329530874912561325670400000000000000000000000000000000000000000000000000000000000⟩]
private noncomputable def tree0 : TapeTree := .direct (candidateRows ibox0)
attribute [irreducible] tree0
private theorem sign_0 : (computed denominator ibox0).value.hi ≤ 0 := by decide +kernel
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 85 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox0,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox0).value.hi denominator_positive).1 sign_0
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (5208333333333333/125000000000000000 : ℚ) (6510416666666667/125000000000000000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 85 = e93 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (5208333333333333/125000000000000000 : ℚ) (6510416666666667/125000000000000000 : ℚ)) x → eval e93 x ≤ 0 := by
  have hb := h.child_4 tape 85 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell19_high_first_bottom

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell19_high_first_bottom
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((5208333333333333/125000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((6510416666666667/125000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 19 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 19 p)
    (hkb : ((6510416666666667/125000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((5208333333333333/125000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ bStar), firstResidual (0 : Fin 9) a p r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell19_high_first_bottom.cell_bound h.child_8 h.child_9 (Cell19_high_first_bottom.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell19_high_first_bottom
