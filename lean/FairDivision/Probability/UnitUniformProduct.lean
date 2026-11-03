import FairDivision.Probability.FiniteDisjointBlocks
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Finite products of continuous uniform unit weights

Concrete probability leaves used by BF Section 7. The law is restricted
Lebesgue measure on (0,1), whose mass is already one. Existing Mathlib
finite-product measures provide coordinate laws, independence, and Tonelli;
PFR supplies independence of functions of disjoint finite coordinate blocks.
No random oracle, unspecified sampler, or probabilistic existence premise
is added.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Probability.UnitUniformProduct

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set

/-- The actual continuous Uniform(0,1) probability law. -/
def unitLaw : Measure ℝ:=volume.restrict (Ioo 0 1)

instance : IsProbabilityMeasure unitLaw := by
  constructor
  norm_num [unitLaw,Real.volume_Ioo]

instance : NullSingletonClass unitLaw:=by unfold unitLaw;infer_instance

def law (ι : Type*) [Fintype ι] : Measure (ι→ℝ):=Measure.pi (fun _ : ι=>unitLaw)

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (law ι):=by
  unfold law
  infer_instance

theorem coordinate_law {ι : Type*} [Fintype ι] (i : ι) :
    (law ι).map (fun w=>w i)=unitLaw :=
  (measurePreserving_eval (fun _ : ι=>unitLaw) i).map_eq

theorem independent_coordinates {ι : Type*} [Fintype ι] :
    iIndepFun (fun i (w : ι→ℝ)=>w i) (law ι) :=
  iIndepFun_pi (fun _=>measurable_id.aemeasurable)

/-- An injective coordinate selection has exactly the smaller product
law, even when unused coordinates remain in the physical sample. -/
theorem selection_law {ι κ : Type*} [Fintype ι] [Fintype κ]
    (select : ι→κ) (hSelect : Function.Injective select) :
    (law κ).map (fun w i=>w (select i))=law ι := by
  have hIndependent:=ProbabilityTheory.iIndepFun.precomp hSelect
    (independent_coordinates (ι:=κ))
  have hMap:=ProbabilityTheory.iIndepFun.map_fun_eq_pi_map
    (fun i=>(measurable_pi_apply (select i)).aemeasurable) hIndependent
  rw [hMap]
  change Measure.pi (fun i=>(law κ).map (fun w=>w (select i)))=
    Measure.pi (fun _ : ι=>unitLaw)
  congr 1
  funext i
  exact coordinate_law (select i)

/-- Every coordinate lies in the actual open unit interval almost surely. -/
theorem ae_unit {ι : Type*} [Fintype ι] :
    ∀ᵐ w ∂law ι,∀i : ι,0<w i ∧w i<1 := by
  apply Filter.eventually_all.mpr
  intro i
  have hUnit : ∀ᵐ x ∂unitLaw,x∈Ioo (0 : ℝ) 1:=
    ae_restrict_mem measurableSet_Ioo
  simpa only [law,Set.mem_Ioo] using
    (Measure.tendsto_eval_ae_ae (μ:=fun _ : ι=>unitLaw) (i:=i)).eventually hUnit

/-- Independent continuous coordinates have no ties; the null diagonal
is computed directly by the existing product-measure fiber formula. -/
theorem coordinate_tie_null {ι : Type*} [Fintype ι] (i j : ι) (hij : i≠j) :
    law ι {w | w i=w j}=0 := by
  let diagonal : Set (ℝ×ℝ):={z | z.1=z.2}
  have hMeasurable : MeasurableSet diagonal:=(isClosed_eq continuous_fst continuous_snd).measurableSet
  have hNull : unitLaw.prod unitLaw diagonal=0 := by
    rw [Measure.prod_apply hMeasurable]
    have hFiber (x : ℝ) : Prod.mk x ⁻¹' diagonal={x} := by
      ext y
      simp [diagonal,eq_comm]
    simp only [hFiber,measure_singleton,lintegral_zero]
  have hMap:=((independent_coordinates (ι:=ι)).indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  rw [coordinate_law,coordinate_law] at hMap
  rw [←hMap,Measure.map_apply
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) hMeasurable] at hNull
  exact hNull

theorem ae_distinct {ι : Type*} [Fintype ι] :
    ∀ᵐ w ∂law ι,Function.Injective w := by
  have hEach : ∀i j : ι,∀ᵐ w ∂law ι,i≠j→w i≠w j := by
    intro i j
    by_cases hij:i=j
    · exact Filter.Eventually.of_forall (fun _ h=>False.elim (h hij))
    · exact (measure_eq_zero_iff_ae_notMem.mp (coordinate_tie_null i j hij)).mono
        (fun w hw _=>hw)
  filter_upwards [Filter.eventually_all.mpr (fun i=>Filter.eventually_all.mpr (hEach i))]
    with w hw
  intro i j hEq
  by_contra hij
  exact hw i j hij hEq

/-- The two half-intervals have exactly the same probability. -/
theorem unitLaw_low : unitLaw (Iio ((1 : ℝ)/2))=(2 : ℝ≥0∞)⁻¹ := by
  rw [unitLaw,Measure.restrict_apply measurableSet_Iio]
  have hSet : Iio ((1 : ℝ)/2)∩Ioo 0 1=Ioo 0 ((1 : ℝ)/2) := by
    ext x
    simp only [mem_inter_iff,mem_Iio,mem_Ioo]
    constructor
    · rintro ⟨hHalf,hZero,hOne⟩
      exact ⟨hZero,hHalf⟩
    · rintro ⟨hZero,hHalf⟩
      exact ⟨hHalf,hZero,by linarith⟩
  rw [hSet,Real.volume_Ioo]
  norm_num
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem unitLaw_high : unitLaw (Ioi ((1 : ℝ)/2))=(2 : ℝ≥0∞)⁻¹ := by
  rw [unitLaw,Measure.restrict_apply measurableSet_Ioi]
  have hSet : Ioi ((1 : ℝ)/2)∩Ioo 0 1=Ioo ((1 : ℝ)/2) 1 := by
    ext x
    simp only [mem_inter_iff,mem_Ioi,mem_Ioo]
    constructor
    · rintro ⟨hHalf,hZero,hOne⟩
      exact ⟨hHalf,hOne⟩
    · rintro ⟨hHalf,hOne⟩
      exact ⟨hHalf,by linarith,hOne⟩
  rw [hSet,Real.volume_Ioo]
  norm_num
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- none is an unconstrained coordinate; true/false request the upper
or lower half. Majority-tied mixed sets use none. -/
def interval : Option Bool→Set ℝ
  | none=>univ
  | some false=>Iio ((1 : ℝ)/2)
  | some true=>Ioi ((1 : ℝ)/2)

theorem measurable_interval (side : Option Bool) : MeasurableSet (interval side) := by
  cases side with
  | none=>exact MeasurableSet.univ
  | some b=>
      cases b with
      | false=>exact measurableSet_Iio
      | true=>exact measurableSet_Ioi

theorem interval_mass_lower (side : Option Bool) :
    (2 : ℝ≥0∞)⁻¹≤unitLaw (interval side) := by
  cases side with
  | none=>norm_num [interval]
  | some b=>cases b <;> simp only [interval,unitLaw_low,unitLaw_high,le_refl]

def box {ι : Type*} (side : ι→Option Bool) : Set (ι→ℝ):=
  univ.pi (fun i=>interval (side i))

theorem measurable_box {ι : Type*} [Fintype ι] (side : ι→Option Bool) :
    MeasurableSet (box side):=
  MeasurableSet.univ_pi (fun i=>measurable_interval (side i))

/-- At least 2^(−number of coordinates), including unconstrained ones. -/
theorem box_mass_lower {ι : Type*} [Fintype ι] (side : ι→Option Bool) :
    ((2 : ℝ≥0∞)⁻¹)^Fintype.card ι≤law ι (box side) := by
  rw [law,box,Measure.pi_pi]
  simpa only [Finset.prod_const,Finset.card_univ] using
    Finset.prod_le_prod' (fun i (_ : i∈Finset.univ)=>interval_mass_lower (side i))

/-- Exact manuscript independence calculation for a FIXED conditioning
value: disjoint mixed-set coordinate blocks, arbitrary fixed orientations,
and a common upper bound B on the number of coordinates per pair. -/
theorem avoid_disjoint_boxes_le {ι P : Type*} [Fintype ι] [Fintype P]
    (blocks : P→Finset ι) (hDisjoint : Set.PairwiseDisjoint univ blocks)
    (side : (p : P)→blocks p→Option Bool) (B : ℕ)
    (hCard : ∀p,(blocks p).card≤B) :
    law ι {w | ∀p : P,(fun i : blocks p=>w i)∉box (side p)}≤
      (1-((2 : ℝ≥0∞)⁻¹)^B)^Fintype.card P := by
  classical
  let restrict (p : P) (w : ι→ℝ) : blocks p→ℝ:=fun i=>w i
  have hIndependent:=(independent_coordinates (ι:=ι)).finsets blocks hDisjoint
    (fun i=>measurable_pi_apply i)
  have hProduct : law ι {w | ∀p : P,restrict p w∈(box (side p))ᶜ}=
      ∏p : P,law ι (restrict p ⁻¹' (box (side p))ᶜ) := by
    have h:=hIndependent.measure_inter_preimage_eq_mul Finset.univ
      (sets:=fun p=>(box (side p))ᶜ) (fun p hp=>(measurable_box (side p)).compl)
    have hSet : (⋂p∈(Finset.univ : Finset P),restrict p ⁻¹' (box (side p))ᶜ)=
        {w | ∀p : P,restrict p w∈(box (side p))ᶜ} := by
      ext w
      simp
    rw [hSet] at h
    exact h
  change law ι {w | ∀p : P,restrict p w∈(box (side p))ᶜ}≤_
  rw [hProduct]
  have hEach (p : P) :
      law ι (restrict p ⁻¹' (box (side p))ᶜ)≤1-((2 : ℝ≥0∞)⁻¹)^B := by
    have hMeasurable : Measurable (restrict p):=by
      apply measurable_pi_lambda
      intro i
      exact measurable_pi_apply i.val
    have hMap : (law ι).map (restrict p)=law (blocks p):=
      selection_law Subtype.val Subtype.val_injective
    have hPullback : law ι (restrict p ⁻¹' (box (side p))ᶜ)=
        law (blocks p) (box (side p))ᶜ := by
      rw [←hMap,Measure.map_apply hMeasurable (measurable_box (side p)).compl]
    rw [hPullback,prob_compl_eq_one_sub (measurable_box (side p))]
    have hExponent : Fintype.card (blocks p)≤B:=by
      simpa only [Fintype.card_coe] using hCard p
    have hPower : ((2 : ℝ≥0∞)⁻¹)^B≤((2 : ℝ≥0∞)⁻¹)^Fintype.card (blocks p):=
      pow_le_pow_of_le_one (by positivity) (by norm_num) hExponent
    exact tsub_le_tsub_left (hPower.trans (box_mass_lower (side p))) 1
  calc
    (∏p : P,law ι (restrict p ⁻¹' (box (side p))ᶜ))≤
        ∏_p : P,(1-((2 : ℝ≥0∞)⁻¹)^B) :=
      Finset.prod_le_prod' (fun p _=>hEach p)
    _=(1-((2 : ℝ≥0∞)⁻¹)^B)^Fintype.card P := by
      rw [Finset.prod_const,Finset.card_univ]

end FairDivision.Probability.UnitUniformProduct
