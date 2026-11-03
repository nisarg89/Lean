import FairDivision.BF.SwapUnconditionalProbability
import FairDivision.BF.SwapFirstMomentAsymptotic

/-!
# Swap impossibility by the first-moment method

Z is the finite sum of indicators of equal-q t-swap allocations, exactly
as in the manuscript. The integrated fixed-allocation estimate bounds its
expectation by n^(nq)(1−η(q))^choose(n,2). Once this is below one, there is
an actual bounded realization with no such allocation. The deterministic
valuation lemmas already give normalization, strict monotonicity,
submodularity, and EFX of EVERY equal-q allocation in that realization.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.SwapThresholdNegative

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open SwapConditionalProbability SwapUnconditionalProbability
open FairDivision.Probability.UnitUniformProduct

variable {n m q t : ℕ}

def candidateEvent (t q : ℕ) (A : Allocation n m) : Set (Finset (Fin m)→ℝ) := by
  classical
  exact if HasEqualBundleSize A q then
    {W | IsTSwapEF t (fun _=>SwapPerturbedValuation.value q W) A} else ∅

theorem measurable_candidateEvent (A : Allocation n m) :
    MeasurableSet (candidateEvent t q A) := by
  classical
  unfold candidateEvent
  split_ifs
  · exact measurable_fair_event A
  · exact MeasurableSet.empty

/-- Literal number of successful candidate allocations, as a finite sum
of 0/1 indicators in the nonnegative integral's coefficient type. -/
def successfulCount (t q : ℕ) (W : Finset (Fin m)→ℝ) : ℝ≥0∞ :=
  ∑A : Allocation n m,(candidateEvent t q A).indicator 1 W

/-- The finite set counted by Z. Its natural cardinality gives the literal
nonnegative integer random variable from the manuscript, before coercion to
the nonnegative integral's coefficient type. -/
def successfulAllocations (t q : ℕ) (W : Finset (Fin m)→ℝ) :
    Finset (Allocation n m) := by
  classical
  exact Finset.univ.filter (fun A => W∈candidateEvent t q A)

@[simp] theorem mem_successfulAllocations (A : Allocation n m)
    (W : Finset (Fin m)→ℝ) :
    A∈successfulAllocations t q W ↔ HasEqualBundleSize A q ∧
      IsTSwapEF t (fun _=>SwapPerturbedValuation.value q W) A := by
  classical
  by_cases hSize : HasEqualBundleSize A q <;>
    simp [successfulAllocations,candidateEvent,hSize]

/-- The existing indicator sum is exactly the natural number of successful
allocations, including n=0 or m=0 and the empty candidate set. -/
theorem successfulCount_eq_card (W : Finset (Fin m)→ℝ) :
    successfulCount (n:=n) t q W=
      ((successfulAllocations (n:=n) t q W).card : ℝ≥0∞) := by
  classical
  unfold successfulCount successfulAllocations
  simp only [Set.indicator_apply,Pi.one_apply]
  exact Finset.sum_boole (fun A : Allocation n m => W∈candidateEvent t q A) Finset.univ

/-- The unrestricted owner-map count used by the paper's crude union bound.
The equal-size restriction is imposed only by candidateEvent. -/
theorem allocation_card : Fintype.card (Allocation n m)=n^m := by
  change Fintype.card (Fin m→Fin n)=n^m
  simp only [Fintype.card_fun,Fintype.card_fin]

/-- Exact linearity of the finite indicator expectation, before applying
any bound on a fixed allocation's probability. -/
theorem expected_count_eq_sum :
    (∫⁻W : Finset (Fin m)→ℝ,successfulCount (n:=n) t q W ∂law (Finset (Fin m)))=
      ∑A : Allocation n m,law (Finset (Fin m)) (candidateEvent t q A) := by
  classical
  unfold successfulCount
  rw [lintegral_finsetSum
    (f:=fun A : Allocation n m =>
      (candidateEvent t q A).indicator (1 : (Finset (Fin m)→ℝ)→ℝ≥0∞))
    Finset.univ
    (fun A _ => measurable_const.indicator (measurable_candidateEvent A))]
  apply Finset.sum_congr rfl
  intro A _
  exact lintegral_indicator_one (measurable_candidateEvent A)

theorem candidate_measure_le (hThreshold : 2*t+1≤q) (A : Allocation n m) :
    law (Finset (Fin m)) (candidateEvent t q A)≤(1-eta q)^(n.choose 2) := by
  classical
  unfold candidateEvent
  split_ifs with hSize
  · exact fairness_probability_bound A hThreshold hSize
  · simp

/-- Actual linearity of expectation and the literal n^m allocation count. -/
theorem expected_count_le (hThreshold : 2*t+1≤q) :
    (∫⁻W : Finset (Fin m)→ℝ,successfulCount (n:=n) t q W ∂law (Finset (Fin m)))≤
      (n : ℝ≥0∞)^m*(1-eta q)^(n.choose 2) := by
  classical
  rw [expected_count_eq_sum]
  calc
    (∑A : Allocation n m,law (Finset (Fin m)) (candidateEvent t q A))≤
        ∑_A : Allocation n m,(1-eta q)^(n.choose 2) :=
      Finset.sum_le_sum (fun A hA=>candidate_measure_le hThreshold A)
    _=(n : ℝ≥0∞)^m*(1-eta q)^(n.choose 2) := by
      simp only [Finset.sum_const,Finset.card_univ,allocation_card,
        nsmul_eq_mul,Nat.cast_pow]

/-- Any actual successful candidate contributes one to Z. -/
theorem one_le_count_of_candidate (A : Allocation n m) (W : Finset (Fin m)→ℝ)
    (hSize : HasEqualBundleSize A q)
    (hFair : IsTSwapEF t (fun _=>SwapPerturbedValuation.value q W) A) :
    1 ≤ successfulCount (n:=n) t q W := by
  classical
  have hMem : W∈candidateEvent t q A:=by simp only [candidateEvent,if_pos hSize];exact hFair
  have hSingle : (candidateEvent t q A).indicator (1 : (Finset (Fin m)→ℝ)→ℝ≥0∞) W≤
      ∑B : Allocation n m,(candidateEvent t q B).indicator 1 W :=
    Finset.single_le_sum (fun B _ => (show (0 : ℝ≥0∞)≤
      (candidateEvent t q B).indicator 1 W from zero_le)) (Finset.mem_univ A)
  simpa only [successfulCount,Set.indicator_of_mem hMem,Pi.one_apply] using hSingle

/-- The first-moment existence step uses the actual unit-law support and
actual indicator sum; no abstract random-valuation premise remains. -/
theorem exists_bad_realization (hThreshold : 2*t+1≤q)
    (hCount : (n : ℝ≥0∞)^m*(1-eta q)^(n.choose 2)<1) :
    ∃W : Finset (Fin m)→ℝ,(∀S,0≤W S ∧W S<1) ∧
      ∀A : Allocation n m,HasEqualBundleSize A q→
        ¬IsTSwapEF t (fun _=>SwapPerturbedValuation.value q W) A := by
  classical
  by_contra hNo
  push_neg at hNo
  have hAtLeastOne : ∀ᵐW ∂law (Finset (Fin m)),1 ≤ successfulCount (n:=n) t q W := by
    filter_upwards [ae_unit (ι:=Finset (Fin m))] with W hUnit
    have hBounded : ∀S,0≤W S ∧W S<1:=fun S=>⟨(hUnit S).1.le,(hUnit S).2⟩
    obtain ⟨A,hSize,hFair⟩:=hNo W hBounded
    exact one_le_count_of_candidate A W hSize hFair
  have hIntegral : (1 : ℝ≥0∞)≤
      ∫⁻W : Finset (Fin m)→ℝ,successfulCount (n:=n) t q W ∂law (Finset (Fin m)) := by
    simpa only [lintegral_const,measure_univ,mul_one] using lintegral_mono_ae hAtLeastOne
  exact (not_lt_of_ge (hIntegral.trans (expected_count_le hThreshold))) hCount

/-- Exact manuscript negative theorem, including EVERY sufficiently
large n and the EFX separation for the SAME common valuation. -/
theorem eventually_exists_submodular_no_tSwapEF
    (t q : ℕ) (ht : 1≤t) (hThreshold : 2*t+1≤q) :
    ∀ᶠn : ℕ in atTop,∃v : Finset (Fin (n*q))→ℝ,
      IsNormalized v ∧StrictMono v ∧IsBundleSubmodular v ∧
      ∀A : Allocation n (n*q),HasEqualBundleSize A q→
        IsBundleEFX (fun _=>v) A ∧¬IsTSwapEF t (fun _=>v) A := by
  filter_upwards [SwapFirstMomentAsymptotic.eventually_count_probability_lt_one q]
    with n hn
  obtain ⟨W,hW,hBad⟩:=exists_bad_realization (n:=n) (m:=n*q) hThreshold hn
  refine ⟨SwapPerturbedValuation.value q W,
    SwapPerturbedValuation.normalized (by omega : 0<q) W,
    SwapPerturbedValuation.strictly_monotone W hW,
    SwapPerturbedValuation.submodular W hW,?_⟩
  intro A hSize
  exact ⟨SwapPerturbedValuation.every_equal_allocation_EFX W hW A hSize,hBad A hSize⟩

/-- The same theorem with the natural-language 'every sufficiently large'
quantifier expanded as an explicit threshold N. -/
theorem exists_threshold_submodular_no_tSwapEF
    (t q : ℕ) (ht : 1≤t) (hThreshold : 2*t+1≤q) :
    ∃N : ℕ,∀n≥N,∃v : Finset (Fin (n*q))→ℝ,
      IsNormalized v ∧StrictMono v ∧IsBundleSubmodular v ∧
      ∀A : Allocation n (n*q),HasEqualBundleSize A q→
        IsBundleEFX (fun _=>v) A ∧¬IsTSwapEF t (fun _=>v) A :=
  Filter.eventually_atTop.mp (eventually_exists_submodular_no_tSwapEF t q ht hThreshold)

end FairDivision.BF.SwapThresholdNegative
