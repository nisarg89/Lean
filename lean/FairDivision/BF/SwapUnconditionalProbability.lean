import FairDivision.BF.SwapConditionalProbability

/-!
# Integrating the actual conditional swap-obstruction estimate

The original bundle weights and all remaining coordinates are sampled
independently from the actual continuous unit law. A literal injective
selection of coordinates proves that their splice has exactly the full
product law, even though the unused z copies of original coordinates
remain in the physical sample. Tonelli integrates the previously proved
conditional bound; the original weights are distinct almost surely.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.SwapUnconditionalProbability

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set
open FairDivision.BF SwapObstruction SwapConditionalProbability
open FairDivision.Probability.UnitUniformProduct

variable {n m q t : ℕ}

/-- One literal source coordinate for each output random weight. -/
def sourceIndex (A : Allocation n m) (U : Finset (Fin m)) : Fin n⊕Finset (Fin m) := by
  classical
  exact if h:∃i : Fin n,bundle A i=U then Sum.inl h.choose else Sum.inr U

theorem sourceIndex_injective (A : Allocation n m) : Function.Injective (sourceIndex A) := by
  classical
  intro U V hEq
  by_cases hU:∃i : Fin n,bundle A i=U <;>
    by_cases hV:∃i : Fin n,bundle A i=V
  · simp only [sourceIndex,dif_pos hU,dif_pos hV,Sum.inl.injEq] at hEq
    exact hU.choose_spec.symm.trans ((congrArg (bundle A) hEq).trans hV.choose_spec)
  · simp only [sourceIndex,dif_pos hU,dif_neg hV,Sum.inl_ne_inr] at hEq
  · simp only [sourceIndex,dif_neg hU,dif_pos hV,Sum.inr_ne_inl] at hEq
  · simpa only [sourceIndex,dif_neg hU,dif_neg hV,Sum.inr.injEq] using hEq

/-- Exact full product law of the literal conditioning splice. -/
theorem realize_measurePreserving (A : Allocation n m) :
    MeasurePreserving (fun bz : (Fin n→ℝ)×(Finset (Fin m)→ℝ)=>realize A bz.1 bz.2)
      ((law (Fin n)).prod (law (Finset (Fin m)))) (law (Finset (Fin m))) := by
  classical
  have hSelect : MeasurePreserving
      (fun w : (Fin n⊕Finset (Fin m))→ℝ=>fun U=>w (sourceIndex A U))
      (law (Fin n⊕Finset (Fin m))) (law (Finset (Fin m))) :=
    ⟨by fun_prop,selection_law (sourceIndex A) (sourceIndex_injective A)⟩
  have hSplit : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin n⊕Finset (Fin m)=>ℝ)).symm
      ((law (Fin n)).prod (law (Finset (Fin m))))
      (law (Fin n⊕Finset (Fin m))) := by
    simpa only [law] using measurePreserving_sumPiEquivProdPi_symm
      (fun _ : Fin n⊕Finset (Fin m)=>unitLaw)
  have hFunction :
      (fun bz : (Fin n→ℝ)×(Finset (Fin m)→ℝ)=>realize A bz.1 bz.2)=
        (fun w : (Fin n⊕Finset (Fin m))→ℝ=>fun U=>w (sourceIndex A U)) ∘
          (MeasurableEquiv.sumPiEquivProdPi
            (fun _ : Fin n⊕Finset (Fin m)=>ℝ)).symm := by
    funext bz U
    simp only [Function.comp_apply,sourceIndex,realize]
    split_ifs <;> rfl
  rw [hFunction]
  exact hSelect.comp hSplit

/-- The valuation is an actual measurable affine function of its one
q-layer coordinate. All other baseline terms are literal constants. -/
theorem measurable_value (S : Finset (Fin m)) :
    Measurable (fun W : Finset (Fin m)→ℝ=>SwapPerturbedValuation.value q W S) := by
  unfold SwapPerturbedValuation.value SwapPerturbedValuation.noise
  split_ifs <;> fun_prop

/-- The actual t-swap predicate is measurable: its witnesses range over
finite item subsets and it uses finitely many continuous inequalities. -/
theorem measurable_fair_event (A : Allocation n m) :
    MeasurableSet {W : Finset (Fin m)→ℝ |
      IsTSwapEF t (fun _=>SwapPerturbedValuation.value q W) A} := by
  classical
  let legal (i j : Fin n) (X Y : Finset (Fin m)) : Prop :=
    X⊆bundle A i ∧Y⊆bundle A j ∧1≤X.card ∧X.card=Y.card ∧X.card≤t
  have hSet : {W : Finset (Fin m)→ℝ |
      IsTSwapEF t (fun _=>SwapPerturbedValuation.value q W) A}=
      ⋂i : Fin n,⋂j : Fin n,
        ({W | SwapPerturbedValuation.value q W (bundle A i)<
          SwapPerturbedValuation.value q W (bundle A j)})ᶜ ∪
        ⋃X : Finset (Fin m),⋃Y : Finset (Fin m),
          {W | legal i j X Y ∧
            SwapPerturbedValuation.value q W ((bundle A j\Y)∪X)≤
              SwapPerturbedValuation.value q W ((bundle A i\X)∪Y)} := by
    ext W
    constructor
    · intro hFair
      apply Set.mem_iInter.mpr
      intro i
      apply Set.mem_iInter.mpr
      intro j
      by_cases hEnvy : SwapPerturbedValuation.value q W (bundle A i)<
          SwapPerturbedValuation.value q W (bundle A j)
      · obtain ⟨X,Y,hX,hY,hNonempty,hCard,hBudget,hValue⟩:=hFair i j hEnvy
        apply Or.inr
        apply Set.mem_iUnion.mpr
        refine ⟨X,Set.mem_iUnion.mpr ⟨Y,?_⟩⟩
        exact ⟨⟨hX,hY,hNonempty,hCard,hBudget⟩,hValue⟩
      · exact Or.inl hEnvy
    · intro hEvent i j hEnvy
      have hPair:=Set.mem_iInter.mp (Set.mem_iInter.mp hEvent i) j
      rcases hPair with hNotEnvy | hSwap
      · exact (hNotEnvy hEnvy).elim
      · obtain ⟨X,hX⟩:=Set.mem_iUnion.mp hSwap
        obtain ⟨Y,hY⟩:=Set.mem_iUnion.mp hX
        exact ⟨X,Y,hY.1.1,hY.1.2.1,hY.1.2.2.1,
          hY.1.2.2.2.1,hY.1.2.2.2.2,hY.2⟩
  rw [hSet]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.union
  · exact (measurableSet_lt (measurable_value _) (measurable_value _)).compl
  · apply MeasurableSet.iUnion
    intro X
    apply MeasurableSet.iUnion
    intro Y
    by_cases hLegal:legal i j X Y
    · simpa only [hLegal,true_and] using
        measurableSet_le (measurable_value ((bundle A j\Y)∪X))
          (measurable_value ((bundle A i\X)∪Y))
    · simp only [hLegal,false_and,Set.setOf_false]
      exact MeasurableSet.empty

/-- The manuscript's unconditional probability estimate for any fixed
allocation with equal bundle cardinalities. Conditional independence is
integrated over the ACTUAL original continuous weights, not postulated. -/
theorem fairness_probability_bound (A : Allocation n m)
    (hThreshold : 2*t+1≤q) (hSize : HasEqualBundleSize A q) :
    law (Finset (Fin m)) {W |
      IsTSwapEF t (fun _=>SwapPerturbedValuation.value q W) A}≤
      (1-eta q)^(n.choose 2) := by
  let event : Set (Finset (Fin m)→ℝ):=
    {W | IsTSwapEF t (fun _=>SwapPerturbedValuation.value q W) A}
  have hMeasurable : MeasurableSet event:=measurable_fair_event A
  have hSplice:=realize_measurePreserving A
  rw [←hSplice.map_eq,Measure.map_apply hSplice.measurable hMeasurable,
    Measure.prod_apply (hMeasurable.preimage hSplice.measurable)]
  calc
    (∫⁻b : Fin n→ℝ,law (Finset (Fin m))
      {z | IsTSwapEF t (fun _=>SwapPerturbedValuation.value q (realize A b z)) A}
      ∂law (Fin n))≤∫⁻_ : Fin n→ℝ,(1-eta q)^(n.choose 2) ∂law (Fin n) := by
      apply lintegral_mono_ae
      exact (ae_distinct (ι:=Fin n)).mono (fun b hb=>
        conditional_fairness_bound A hThreshold hSize b hb)
    _=(1-eta q)^(n.choose 2) := by simp

end FairDivision.BF.SwapUnconditionalProbability
