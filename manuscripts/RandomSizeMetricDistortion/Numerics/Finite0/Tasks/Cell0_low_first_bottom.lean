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
namespace Cell0_low_first_bottom
private noncomputable def qValues : Fin 1 → ℚ := ![(0/1 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics0.e2 qValues
private noncomputable abbrev e6 : PolyExpr := SharedFiniteSemantics0.e6 qValues
private noncomputable abbrev e12 : PolyExpr := SharedFiniteSemantics0.e12 qValues
private noncomputable abbrev e16 : PolyExpr := SharedFiniteSemantics0.e16 qValues
private noncomputable abbrev e89 : PolyExpr := SharedFiniteSemantics0.e89 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics0.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics0.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics0.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics0.node_4 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics0.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics0.node_7 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics0.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics0.node_11 qValues
private noncomputable abbrev node_12 := SharedFiniteSemantics0.node_12 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics0.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics0.node_15 qValues
private noncomputable abbrev node_16 := SharedFiniteSemantics0.node_16 qValues
private noncomputable abbrev node_54 := SharedFiniteSemantics0.node_54 qValues
private noncomputable abbrev node_55 := SharedFiniteSemantics0.node_55 qValues
private noncomputable abbrev node_56 := SharedFiniteSemantics0.node_56 qValues
private noncomputable abbrev node_57 := SharedFiniteSemantics0.node_57 qValues
private noncomputable abbrev node_58 := SharedFiniteSemantics0.node_58 qValues
private noncomputable abbrev node_59 := SharedFiniteSemantics0.node_59 qValues
private noncomputable abbrev node_60 := SharedFiniteSemantics0.node_60 qValues
private noncomputable abbrev node_61 := SharedFiniteSemantics0.node_61 qValues
private noncomputable abbrev node_62 := SharedFiniteSemantics0.node_62 qValues
private noncomputable abbrev node_67 := SharedFiniteSemantics0.node_67 qValues
private noncomputable abbrev node_68 := SharedFiniteSemantics0.node_68 qValues
private noncomputable abbrev node_69 := SharedFiniteSemantics0.node_69 qValues
private noncomputable abbrev node_86 := SharedFiniteSemantics0.node_86 qValues
private noncomputable abbrev node_87 := SharedFiniteSemantics0.node_87 qValues
private noncomputable abbrev node_88 := SharedFiniteSemantics0.node_88 qValues
private noncomputable abbrev node_89 := SharedFiniteSemantics0.node_89 qValues
private noncomputable abbrev semantic_H_37 := SharedFiniteSemantics0.semantic_H_37 qValues
private noncomputable abbrev semantic_H_53 := SharedFiniteSemantics0.semantic_H_53 qValues
private noncomputable abbrev semantic_psi_85 := SharedFiniteSemantics0.semantic_psi_85 qValues
private noncomputable def aPoint (x : Fin 4 → ℝ) : ℝ := x 0*x 1
private noncomputable def rPoint (x : Fin 4 → ℝ) : ℝ := ((49/100 : ℚ) : ℝ)+(((2840189/5000000 : ℚ) : ℝ)-((49/100 : ℚ) : ℝ))*x 2
private noncomputable def yPoint (x : Fin 4 → ℝ) : ℝ := aPoint x+1-x 0
private theorem point_6 (x : Fin 4 → ℝ) : eval e6 x = aPoint x := by
  simp only [node_2,node_3,node_6] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_12 (x : Fin 4 → ℝ) : eval e12 x = rPoint x := by
  simp only [node_4,node_7,node_10,node_11,node_12] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_2 (x : Fin 4 → ℝ) : eval e2 x = x 0 := by
  simp only [node_2] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_16 (x : Fin 4 → ℝ) : eval e16 x = yPoint x := by
  simp only [node_1,node_2,node_3,node_6,node_14,node_15,node_16] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem price_lambda_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceLambda 0 p = 4*(145513/100000 : ℝ)/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell0,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 0 p = (145513/100000 : ℝ)*(1+4*p-(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell0,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e89 x = (1)*(aPoint x+priceLambda 0 (x 0)*(HStar (yPoint x)-HStar (aPoint x))+priceTau 0 (x 0)*psiStar (rPoint x)+(0)-(cStar)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_54,node_55,node_56,node_57,node_58,node_59,node_60,node_61,node_62,node_67,node_68,node_69,node_86,node_87,node_88,node_89,semantic_H_37,semantic_H_53,semantic_psi_85,point_6,point_12,point_2,point_16]
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
    (hL : lambdaStar (x 0) = priceLambda 0 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 0 (x 0)) :
    (1)*eval e89 x = (1)*(firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (0/1 : ℚ) (1/4096 : ℚ)) x → eval e89 x ≤ 0)
    (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((0/1 : ℚ) : ℝ) < p ∧ p ≤ ((1/4096 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 0 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 0 p)
    (hk0 : ((1/4096 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((0/1 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ ((49/100 : ℚ) : ℝ)) :
    firstResidual (0 : Fin 9) a p r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨x,hx,hxp,hxa,hxr⟩ := h1 (0/1 : ℚ) (1/4096 : ℚ) ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ) p a r hpcell hk0 hr ha hap hcase
  have hcut : ((1/4096 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,if_pos hcut] using hxa
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,if_pos hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 0 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 0 (x 0) := by simpa only [hxp] using hT
  have hrootb : ((2840189/5000000 : ℚ) : ℝ) ≤ bStar := by norm_num [bStar]
  have hflag : aPoint x ≤ bStar := by rw [hax]; exact (hap.trans (min_le_right _ _)).trans (hr.2.trans hrootb)
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e89 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
  rw [actual_identity hs x hpx hflag hLx hTx] at hv
  simp only [one_mul] at hv
  simpa only [hxp,hax,hrx] using hv
private noncomputable def tape : List TapeOp := [
.const (1/1 : ℚ),
.var 0,
.var 1,
.var 2,
.mul 1 2,
.const (49/100 : ℚ),
.const (390189/5000000 : ℚ),
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
.const (4/1 : ℚ),
.mul 51 1,
.add 0 52,
.const (-1/1 : ℚ),
.add 53 54,
.const (145513/100000 : ℚ),
.mul 56 55,
.const (145513/25000 : ℚ),
.mul 58 50,
.add 4 59,
.const (19/73 : ℚ),
.mul 61 8,
.mul 8 8,
.const (35/146 : ℚ),
.mul 64 63,
.add 62 65,
.mul 63 63,
.mul 67 67,
.mul 68 68,
.mul 69 69,
.const (1/2 : ℚ),
.mul 71 70,
.add 66 72,
.neg 73,
.add 12 74,
.mul 31 75,
.mul 57 76,
.add 60 77,
.const (-113609/200000 : ℚ),
.add 78 79]
private noncomputable def ssaQVals : Fin 16 → ℚ := ![(1/1 : ℚ),(49/100 : ℚ),(390189/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(4/1 : ℚ),(-1/1 : ℚ),(145513/100000 : ℚ),(145513/25000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ),(-113609/200000 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_a51ffb7c57202096.p81 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_a51ffb7c57202096.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 80 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_a51ffb7c57202096.ssa_matches ssaQVals D B

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
private noncomputable def denominator : Int := 29183294757838388933353851123700932280320000000
private theorem denominator_positive : 0 < denominator := by decide +kernel
private noncomputable def candidateRows (B : Fin 4 → FixedTape.I) : List TapeBounds :=
  (FixedTape.rowsAux denominator B [] tape).map (FixedTape.decodeRow denominator)
private theorem root_in_range : 80 < tape.length := by decide +kernel
private theorem references_valid : tapeRefsValidAux 0 tape = true := by decide +kernel
private theorem candidate_valid (h : Needs) (B : Fin 4 → FixedTape.I) :
    tapeCheck (FixedTape.decodeBox denominator B) tape (candidateRows B) = true :=
  h.child_10.1 denominator denominator_positive B tape references_valid
private theorem candidate_root (B : Fin 4 → FixedTape.I) :
    (candidateRows B).getD 80 zeroTapeBounds = FixedTape.decodeRow denominator (computed denominator B) := by
  unfold candidateRows
  rw [←decode_zeroRow denominator,List.getD_map,ssa_matches]
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨0,7124827821737887923182092559497297920000000⟩,⟨0,29183294757838388933353851123700932280320000000⟩,⟨0,29183294757838388933353851123700932280320000000⟩,⟨0,29183294757838388933353851123700932280320000000⟩]
private noncomputable def tree0 : TapeTree := .direct (candidateRows ibox0)
attribute [irreducible] tree0
private theorem sign_0 : (computed denominator ibox0).value.hi ≤ 0 := by decide +kernel
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 80 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox0,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox0).value.hi denominator_positive).1 sign_0
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (0/1 : ℚ) (1/4096 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 80 = e89 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (0/1 : ℚ) (1/4096 : ℚ)) x → eval e89 x ≤ 0 := by
  have hb := h.child_4 tape 80 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell0_low_first_bottom

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell0_low_first_bottom
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((0/1 : ℚ) : ℝ) < p ∧ p ≤ ((1/4096 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 0 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 0 p)
    (hk0 : ((1/4096 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((0/1 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ ((49/100 : ℚ) : ℝ)), firstResidual (0 : Fin 9) a p r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell0_low_first_bottom.cell_bound h.child_8 h.child_9 (Cell0_low_first_bottom.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell0_low_first_bottom
