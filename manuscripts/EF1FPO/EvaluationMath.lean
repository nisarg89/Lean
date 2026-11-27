import EF1FPO.Cutoff
import EF1FPO.LogProgram

/-! Accuracy of polynomial cutoff enumeration and dyadic reply rounding. -/

set_option autoImplicit false

namespace EF1FPO

open scoped BigOperators

noncomputable section

def guardedLogInput (q : ℚ) (t : ℕ) : LogInput :=
  ⟨if 0 < q then q else 1, by split <;> positivity, t⟩

def guardedLog (q : ℚ) (t : ℕ) : ℚ := logApproximation (guardedLogInput q t)

def rowUtility (I : Instance) (i : I.Agent) (S : Finset I.Good) : ℚ :=
  ∑ g ∈ S, I.v i g

def logUtility (I : Instance) (i : I.Agent) (S : Finset I.Good) : ℝ :=
  -Real.log (I.utility i S)

def exactRivalLevel (I : Instance) (z : I.Weights) (i : I.Agent) (g : I.Good) : ℝ :=
  Real.log (max (I.utility i Finset.univ)⁻¹ (I.rivalThreshold (I.expWeights z) i g))

def rationalRivalTerm (I : Instance) (z : I.Agent → ℚ) (t : ℕ)
    (i j : I.Agent) (g : I.Good) : ℚ :=
  let floor := -guardedLog (rowUtility I i Finset.univ) t
  if j ≠ i ∧ 0 < I.v j g then
    max floor (z j + guardedLog (I.v j g) t - guardedLog (I.v i g) t)
  else floor

def rationalRivalLevel (I : Instance) (z : I.Agent → ℚ) (t : ℕ)
    (i : I.Agent) (g : I.Good) : ℚ :=
  Finset.univ.sup' ⟨i, Finset.mem_univ _⟩ (fun j => rationalRivalTerm I z t i j g)

def cutoffThreshold (I : Instance) (z : I.Agent → ℚ) (t : ℕ) (i : I.Agent) : ℚ :=
  let cap := guardedLog 4 t
  if h : (I.positiveGoods i).Nonempty then
    let level := rationalRivalLevel I z t i
    min cap ((I.positiveGoods i).inf' h (fun g =>
      max (-guardedLog (rowUtility I i (cutoff (I.positiveGoods i) level g)) t) (level g)))
  else cap

def EvaluationInput.scaledPoint (d : EvaluationInput) (i : d.prepared.inst.Agent) : ℚ :=
  (logRadius d.prepared.inst : ℚ) * ((d.numerator i : ℚ) / (2 : ℚ) ^ d.inputPrecision)

def EvaluationInput.rawApproximation (d : EvaluationInput) (i : d.prepared.inst.Agent) : ℚ :=
  let I := d.prepared.inst
  let t := d.precision + 4
  let θ := ((2 : ℚ) ^ (16 * weightBits I))⁻¹
  ((1 - θ) * cutoffThreshold I d.scaledPoint t i + θ * guardedLog 4 t) /
    (logRadius I : ℚ)

def roundedNumerator (s : ℕ) (q : ℚ) : ℤ :=
  ⌊(2 : ℚ) ^ s * max (-1) (min 1 q) + 1 / 2⌋

def EvaluationInput.rounded (d : EvaluationInput) : GridNumerator d.prepared.inst.n :=
  fun i => roundedNumerator d.precision (d.rawApproximation i)

theorem guardedLog_error (q : ℚ) (t : ℕ) (hq : 0 < q) :
    |(guardedLog q t : ℝ) - Real.log (q : ℝ)| ≤ precisionError t := by
  simpa only [guardedLog, guardedLogInput, if_pos hq] using
    logApproximation_correct (guardedLogInput q t)

theorem logThreshold_subset (I : Instance) (z : I.Weights) (i : I.Agent)
    (h : (I.positiveBundles i).Nonempty) :
    Real.log (I.threshold (I.expWeights z) i) =
      (I.positiveBundles i).inf' h (subsetScore (exactRivalLevel I z i) (logUtility I i)) := by
  let rival := I.rivalThreshold (I.expWeights z) i
  let seed := (I.utility i Finset.univ)⁻¹
  let payoff (S : Finset I.Good) :=
    max (I.utility i S)⁻¹ (if hS : S.Nonempty then S.sup' hS rival else 0)
  have bundle (S : Finset I.Good) (hS : S ∈ I.positiveBundles i) :
      S.Nonempty ∧ 0 < I.utility i S := by
    have admissible := Finset.mem_erase.mp hS
    have hne := Finset.nonempty_iff_ne_empty.mpr admissible.1
    refine ⟨hne, Finset.sum_pos (fun g hg => ?_) hne⟩
    have positive := (Finset.mem_powerset.mp admissible.2) hg
    exact (Finset.mem_filter.mp positive).2
  have utility_le (S : Finset I.Good) : I.utility i S ≤ I.utility i Finset.univ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun g _ _ => by exact_mod_cast I.nonneg i g)
  obtain ⟨D, hD⟩ := h
  have h : (I.positiveBundles i).Nonempty := ⟨D, hD⟩
  have seedPos : 0 < seed := inv_pos.mpr ((bundle D hD).2.trans_le (utility_le D))
  have payoffPos (S : Finset I.Good) (hS : S ∈ I.positiveBundles i) : 0 < payoff S :=
    (inv_pos.mpr (bundle S hS).2).trans_le (le_max_left _ _)
  have term (S : Finset I.Good) (hS : S ∈ I.positiveBundles i) :
      Real.log (payoff S) = subsetScore (exactRivalLevel I z i) (logUtility I i) S := by
    obtain ⟨hne, hval⟩ := bundle S hS
    have small : seed ≤ (I.utility i S)⁻¹ := inv_anti₀ hval (utility_le S)
    have expLevel (g : I.Good) : Real.exp (exactRivalLevel I z i g) = max seed (rival g) :=
      Real.exp_log (seedPos.trans_le (le_max_left _ _))
    unfold subsetScore logUtility
    rw [dif_pos hne]
    apply Real.exp_injective
    rw [Real.exp_log (payoffPos S hS), Real.exp_strictMono.monotone.map_max,
      Real.exp_neg, Real.exp_log hval,
      Finset.apply_sup'_eq_sup'_comp hne Real.exp (fun _ _ => Real.exp_strictMono.monotone.map_max)]
    simp only [payoff, dif_pos hne, Function.comp_apply, expLevel]
    apply le_antisymm
    · apply max_le (le_max_left _ _)
      exact (Finset.sup'_mono_fun (fun g _ => le_max_right seed (rival g))).trans (le_max_right _ _)
    · refine max_le (le_max_left _ _) (Finset.sup'_le hne _ (fun g hg => ?_))
      exact max_le (small.trans (le_max_left _ _)) ((Finset.le_sup' rival hg).trans (le_max_right _ _))
  obtain ⟨S, hS, hMin⟩ := Finset.exists_mem_eq_inf' h payoff
  change Real.log (if h' : (I.positiveBundles i).Nonempty then (I.positiveBundles i).inf' h' payoff else 0) = _
  rw [dif_pos h, hMin]
  refine le_antisymm (Finset.le_inf' h _ (fun T hT => ?_)) ?_
  · rw [← term T hT]
    exact Real.log_le_log (payoffPos S hS) (hMin.symm.trans_le (Finset.inf'_le payoff hT))
  · rw [term S hS]
    exact Finset.inf'_le _ hS

theorem rationalRivalLevel_error (I : Instance) (z : I.Agent → ℚ) (t : ℕ)
    (i : I.Agent) (g : I.Good) (hRow : I.PositiveRow i) (hOwn : 0 < I.value i g) :
    |(rationalRivalLevel I z t i g : ℝ) - exactRivalLevel I (fun j => (z j : ℝ)) i g| ≤
      2 * precisionError t := by
  let sum : ℝ := I.utility i Finset.univ
  let seed := -Real.log sum
  let ε := precisionError t
  let ne : (Finset.univ : Finset I.Agent).Nonempty := ⟨i, Finset.mem_univ _⟩
  let risky (j : I.Agent) : ℝ :=
    if j = i then 0 else Real.exp (z j : ℝ) * I.value j g / I.value i g
  let truth (j : I.Agent) : ℝ :=
    if j ≠ i ∧ 0 < I.v j g then
      max seed ((z j : ℝ) + Real.log (I.value j g) - Real.log (I.value i g))
    else seed
  have sumPos : 0 < sum := by
    obtain ⟨g', hg'⟩ := hRow
    exact Finset.sum_pos' (fun k _ => by exact_mod_cast I.nonneg i k) ⟨g', Finset.mem_univ _, hg'⟩
  have seedE : Real.exp seed = sum⁻¹ := by simp [seed, Real.exp_neg, Real.exp_log sumPos]
  have each (j : I.Agent) : Real.exp (truth j) = max sum⁻¹ (risky j) := by
    by_cases hj : j = i
    · simp [truth, risky, hj, seedE, inv_nonneg.mpr sumPos.le]
    · by_cases hp : 0 < I.v j g
      · have hp' : 0 < I.value j g := by exact_mod_cast hp
        simp [truth, risky, hj, hp,
          Real.exp_strictMono.monotone.map_max, seedE, Real.exp_sub, Real.exp_add,
          Real.exp_log hp', Real.exp_log hOwn]
      · have hz : I.v j g = 0 := le_antisymm (le_of_not_gt hp) (I.nonneg j g)
        have hz' : I.value j g = 0 := by
          change (I.v j g : ℝ) = 0
          exact_mod_cast hz
        simp [truth, risky, hj, hp, hz', seedE, inv_nonneg.mpr sumPos.le]
  have truthMax : Finset.univ.sup' ne truth = exactRivalLevel I (fun j => (z j : ℝ)) i g := by
    have riskyEq : Finset.univ.sup' ne risky = I.rivalThreshold (I.expWeights (fun j => (z j : ℝ))) i g := rfl
    have ⟨j, hj, best⟩ := Finset.exists_mem_eq_sup' ne risky
    apply Real.exp_injective
    rw [Finset.apply_sup'_eq_sup'_comp ne Real.exp (fun _ _ => Real.exp_strictMono.monotone.map_max)]
    simp only [Function.comp_apply, each, exactRivalLevel, ← riskyEq]
    rw [Real.exp_log ((inv_pos.mpr sumPos).trans_le (le_max_left _ _))]
    refine le_antisymm (Finset.sup'_le ne _ (fun j' hj' => max_le_max le_rfl (Finset.le_sup' risky hj'))) ?_
    rw [best]
    exact Finset.le_sup' (fun x => max sum⁻¹ (risky x)) hj
  let approx (j : I.Agent) : ℝ := rationalRivalTerm I z t i j g
  have epsNonneg : 0 ≤ ε := by dsimp [ε, precisionError]; positivity
  have seedError : |(-(guardedLog (rowUtility I i Finset.univ) t : ℝ)) - seed| ≤ ε := by
    have castSum : (rowUtility I i Finset.univ : ℝ) = sum := by
      simp [rowUtility, sum, Instance.utility, Instance.value, FairDivision.additiveValue]
    have realPos : 0 < (rowUtility I i Finset.univ : ℝ) := by rwa [castSum]
    have ratPos : 0 < rowUtility I i Finset.univ := by exact_mod_cast realPos
    have h := guardedLog_error (rowUtility I i Finset.univ) t ratPos
    rw [castSum] at h
    change |(-(guardedLog (rowUtility I i Finset.univ) t : ℝ)) - (-Real.log sum)| ≤ ε
    rwa [neg_sub_neg, abs_sub_comm]
  have termError (j : I.Agent) : |approx j - truth j| ≤ 2 * ε := by
    by_cases hp : j ≠ i ∧ 0 < I.v j g
    · have own : 0 < I.v i g := by exact_mod_cast hOwn
      let ej := (guardedLog (I.v j g) t : ℝ) - Real.log (I.value j g)
      let ei := (guardedLog (I.v i g) t : ℝ) - Real.log (I.value i g)
      have hj : |ej| ≤ ε := guardedLog_error _ _ hp.2
      have hi : |ei| ≤ ε := guardedLog_error _ _ own
      have hDiff :
          |((z j : ℝ) + (guardedLog (I.v j g) t : ℝ) - (guardedLog (I.v i g) t : ℝ)) -
            ((z j : ℝ) + Real.log (I.value j g) - Real.log (I.value i g))| ≤ 2 * ε := by
        have algebra :
            (z j : ℝ) + (guardedLog (I.v j g) t : ℝ) - (guardedLog (I.v i g) t : ℝ) -
              ((z j : ℝ) + Real.log (I.value j g) - Real.log (I.value i g)) = ej + (-ei) := by
          dsimp [ej, ei]
          ring
        rw [algebra]
        calc
          _ ≤ |ej| + |-ei| := abs_add_le _ _
          _ = |ej| + |ei| := by rw [abs_neg]
          _ ≤ 2 * ε := by linarith only [hj, hi]
      simp only [approx, truth, rationalRivalTerm, if_pos hp, Rat.cast_neg, Rat.cast_max,
        Rat.cast_add, Rat.cast_sub]
      exact (abs_max_sub_max_le_max _ _ _ _).trans
        (max_le (seedError.trans (by linarith only [epsNonneg])) hDiff)
    · simp only [approx, truth, rationalRivalTerm, if_neg hp, Rat.cast_neg]
      exact seedError.trans (by linarith only [epsNonneg])
  rw [rationalRivalLevel,
    Finset.apply_sup'_eq_sup'_comp ne (fun q : ℚ => (q : ℝ)) Rat.cast_max, ← truthMax]
  change |Finset.univ.sup' ne approx - Finset.univ.sup' ne truth| ≤ 2 * ε
  have first : Finset.univ.sup' ne approx ≤ Finset.univ.sup' ne truth + 2 * ε :=
    Finset.sup'_le ne _ (fun j hj => by
      have pointwise := (abs_le.mp (termError j)).2
      have best := Finset.le_sup' truth hj
      linarith only [pointwise, best])
  have second : Finset.univ.sup' ne truth ≤ Finset.univ.sup' ne approx + 2 * ε :=
    Finset.sup'_le ne _ (fun j hj => by
      have pointwise := (abs_le.mp (termError j)).1
      have best := Finset.le_sup' approx hj
      linarith only [pointwise, best])
  exact abs_le.mpr ⟨by linarith only [second], by linarith only [first]⟩

theorem cutoffThreshold_error (I : Instance) (z : I.Agent → ℚ) (t : ℕ) (i : I.Agent)
    (hRow : I.PositiveRow i) :
    |(cutoffThreshold I z t i : ℝ) - I.logThresholdMap (fun j => (z j : ℝ)) i| ≤
      3 * precisionError t := by
  let ε := precisionError t
  let goods := I.positiveGoods i
  let bundles := I.positiveBundles i
  let levels := rationalRivalLevel I z t i
  let estimated (g : I.Good) : ℝ := levels g
  let actual := exactRivalLevel I (fun j => (z j : ℝ)) i
  let cost := logUtility I i
  have epsNonneg : 0 ≤ ε := by dsimp [ε, precisionError]; positivity
  obtain ⟨g, hgp⟩ := hRow
  have inGoods : g ∈ goods := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgp⟩
  have goodsNe : goods.Nonempty := ⟨g, inGoods⟩
  have bundlesNe : bundles.Nonempty := ⟨{g}, Finset.mem_erase.mpr
    ⟨Finset.singleton_ne_empty _, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr inGoods)⟩⟩
  have bundlePositive (A : Finset I.Good) (ne : A.Nonempty) (sub : A ⊆ goods) :
      0 < I.utility i A :=
    Finset.sum_pos (fun x hx => (Finset.mem_filter.mp (sub hx)).2) ne
  have anti (A B : Finset I.Good) (ne : A.Nonempty) (sub : A ⊆ B) (good : B ⊆ goods) :
      cost B ≤ cost A := by
    have hle : I.utility i A ≤ I.utility i B :=
      Finset.sum_le_sum_of_subset_of_nonneg sub (fun x _ _ => by exact_mod_cast I.nonneg i x)
    exact neg_le_neg (Real.log_le_log (bundlePositive A ne (sub.trans good)) hle)
  have infBound {A : Type} (s : Finset A) (hne : s.Nonempty) (f g : A → ℝ) (δ : ℝ)
      (hf : ∀ x ∈ s, f x ≤ g x + δ) : s.inf' hne f ≤ s.inf' hne g + δ := by
    obtain ⟨x, hx, hmin⟩ := Finset.exists_mem_eq_inf' hne g
    rw [hmin]
    exact (Finset.inf'_le f hx).trans (hf x hx)
  have supBound {A : Type} (s : Finset A) (hne : s.Nonempty) (f g : A → ℝ) (δ : ℝ)
      (hf : ∀ x ∈ s, f x ≤ g x + δ) : s.sup' hne f ≤ s.sup' hne g + δ :=
    Finset.sup'_le hne _ (fun x hx => (hf x hx).trans (add_le_add (Finset.le_sup' g hx) le_rfl))
  have infClose {A : Type} (s : Finset A) (hne : s.Nonempty) (f g : A → ℝ) (δ : ℝ)
      (hfg : ∀ x ∈ s, |f x - g x| ≤ δ) : |s.inf' hne f - s.inf' hne g| ≤ δ := by
    have hi := infBound s hne f g δ (fun x hx => by linarith [(abs_le.mp (hfg x hx)).2])
    have lo := infBound s hne g f δ (fun x hx => by linarith [(abs_le.mp (hfg x hx)).1])
    exact abs_le.mpr ⟨by linarith only [lo], by linarith only [hi]⟩
  have subsetClose (S : Finset I.Good) (hS : S ∈ bundles) :
      |subsetScore estimated cost S - subsetScore actual cost S| ≤ 2 * ε := by
    have hadmitted := Finset.mem_erase.mp hS
    have hne := Finset.nonempty_iff_ne_empty.mpr hadmitted.1
    have hsub : S ⊆ goods := Finset.mem_powerset.mp hadmitted.2
    have error (x : I.Good) (hx : x ∈ S) : |estimated x - actual x| ≤ 2 * ε :=
      rationalRivalLevel_error I z t i x ⟨g, hgp⟩ (Finset.mem_filter.mp (hsub hx)).2
    have hi := supBound S hne estimated actual (2 * ε) (fun x hx => by
      linarith [(abs_le.mp (error x hx)).2])
    have lo := supBound S hne actual estimated (2 * ε) (fun x hx => by
      linarith [(abs_le.mp (error x hx)).1])
    have hsup : |S.sup' hne estimated - S.sup' hne actual| ≤ 2 * ε :=
      abs_le.mpr ⟨by linarith only [lo], by linarith only [hi]⟩
    simp only [subsetScore, dif_pos hne]
    exact (abs_max_sub_max_le_max _ _ _ _).trans
      (max_le (by rw [sub_self, abs_zero]; linarith only [epsNonneg]) hsup)
  let exactCut (x : I.Good) : ℝ := max (cost (cutoff goods estimated x)) (estimated x)
  let approxCut (x : I.Good) : ℚ :=
    max (-guardedLog (rowUtility I i (cutoff goods levels x)) t) (levels x)
  have sameCut (x : I.Good) : cutoff goods levels x = cutoff goods estimated x := by
    ext j
    simp [cutoff, estimated]
  have cutClose (x : I.Good) (hx : x ∈ goods) : |(approxCut x : ℝ) - exactCut x| ≤ ε := by
    let A := cutoff goods levels x
    have hA : x ∈ A := by simp [A, cutoff, hx]
    have hU := bundlePositive A ⟨x, hA⟩ (fun y hy => (Finset.mem_filter.mp hy).1)
    have hCast : (rowUtility I i A : ℝ) = I.utility i A := by
      simp [rowUtility, Instance.utility, Instance.value, FairDivision.additiveValue]
    have hReal : 0 < (rowUtility I i A : ℝ) := by rwa [hCast]
    have hRat : 0 < rowUtility I i A := by exact_mod_cast hReal
    have hLog := guardedLog_error (rowUtility I i A) t hRat
    rw [hCast] at hLog
    have hCost : |-(guardedLog (rowUtility I i A) t : ℝ) - cost A| ≤ ε := by
      rw [show cost A = -Real.log (I.utility i A) from rfl, neg_sub_neg, abs_sub_comm]
      exact hLog
    rw [show exactCut x = max (cost A) (estimated x) from by simp only [exactCut, A, sameCut]]
    simp only [approxCut, Rat.cast_max, Rat.cast_neg]
    exact (abs_max_sub_max_le_max _ _ _ _).trans
      (max_le hCost (by rw [sub_self, abs_zero]; exact epsNonneg))
  have exactReduction : bundles.inf' bundlesNe (subsetScore estimated cost) = goods.inf' goodsNe exactCut :=
    cutoff_minimum goods goodsNe estimated cost anti bundlesNe
  have levelError := infClose bundles bundlesNe (subsetScore estimated cost) (subsetScore actual cost)
    (2 * ε) subsetClose
  rw [exactReduction, ← logThreshold_subset I (fun j => (z j : ℝ)) i bundlesNe] at levelError
  have cutoffError := infClose goods goodsNe (fun x => (approxCut x : ℝ)) exactCut ε cutClose
  have totalError :
      |((goods.inf' goodsNe approxCut : ℚ) : ℝ) - Real.log (I.threshold (I.expWeights (fun j => (z j : ℝ))) i)| ≤ 3 * ε := by
    rw [Finset.apply_inf'_eq_inf'_comp goodsNe (fun q : ℚ => (q : ℝ)) Rat.cast_min]
    let a := goods.inf' goodsNe (fun x => (approxCut x : ℝ))
    let b := goods.inf' goodsNe exactCut
    let c := Real.log (I.threshold (I.expWeights (fun j => (z j : ℝ))) i)
    change |a - c| ≤ 3 * ε
    calc
      |a - c| = |(a - b) + (b - c)| := by congr 1 <;> ring
      _ ≤ |a - b| + |b - c| := abs_add_le _ _
      _ ≤ ε + 2 * ε := add_le_add cutoffError levelError
      _ = 3 * ε := by ring
  have capError := guardedLog_error 4 t (by norm_num)
  rw [cutoffThreshold, dif_pos goodsNe, Rat.cast_min]
  change |min (guardedLog 4 t : ℝ) ((goods.inf' goodsNe approxCut : ℚ) : ℝ) -
    min (Real.log 4) (Real.log (I.threshold (I.expWeights (fun j => (z j : ℝ))) i))| ≤ 3 * ε
  exact (abs_min_sub_min_le_max _ _ _ _).trans
    (max_le (capError.trans (by linarith only [epsNonneg])) totalError)

theorem roundedNumerator_error (s : ℕ) (q : ℚ) (v : ℝ) (hv : -1 ≤ v ∧ v ≤ 1)
    (h : |(q : ℝ) - v| ≤ precisionError s / 2) :
    let r := (roundedNumerator s q : ℝ) * precisionError s
    (-1 ≤ r ∧ r ≤ 1) ∧ |r - v| ≤ precisionError s := by
  let c : ℝ := max (-1) (min 1 (q : ℝ))
  let D : ℝ := 2 ^ s
  let δ := precisionError s
  let a : ℚ := (2 : ℚ) ^ s * max (-1) (min 1 q) + 1 / 2
  let k : ℤ := ⌊a⌋
  have hD : 0 < D := by dsimp [D]; positivity
  have hδ : 0 < δ := inv_pos.mpr hD
  have hCancel : D * δ = 1 := mul_inv_cancel₀ hD.ne'
  have hCl : -1 ≤ c := le_max_left _ _
  have hCh : c ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have hCast : (a : ℝ) = D * c + 1 / 2 := by
    simp [a, D, c, Rat.cast_max, Rat.cast_min]
  have hFloor : (k : ℝ) ≤ D * c + 1 / 2 := by
    rw [← hCast]
    exact_mod_cast Int.floor_le a
  have hSucc : D * c + 1 / 2 < (k : ℝ) + 1 := by
    rw [← hCast]
    exact_mod_cast Int.lt_floor_add_one a
  have hRealMin : -D ≤ (k : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hCl hD.le
    have hm' : -(2 : ℝ) ^ s ≤ (a : ℝ) := by rw [hCast]; dsimp only [D] at hm ⊢; linarith
    have hRat : ((-(2 : ℤ) ^ s : ℤ) : ℚ) ≤ a := by exact_mod_cast hm'
    have hInt := Int.le_floor.mpr hRat
    dsimp only [D]
    exact_mod_cast (show -(2 : ℤ) ^ s ≤ k from hInt)
  have hRealMax : (k : ℝ) ≤ D := by
    have hm := mul_le_mul_of_nonneg_left hCh hD.le
    have hLess : (a : ℝ) < (2 : ℝ) ^ s + 1 := by
      rw [hCast]; dsimp only [D] at hm ⊢; linarith
    have hRat : a < (((2 : ℤ) ^ s + 1 : ℤ) : ℚ) := by exact_mod_cast hLess
    have hInt : k < (2 : ℤ) ^ s + 1 := Int.floor_lt.mpr hRat
    dsimp only [D]
    exact_mod_cast (show k ≤ (2 : ℤ) ^ s by omega)
  have hFlat : D * c * δ = c := by rw [mul_comm D c, mul_assoc, hCancel, mul_one]
  have hRound : |(k : ℝ) * δ - c| ≤ δ / 2 := by
    have lo : D * c - 1 / 2 ≤ (k : ℝ) := by linarith only [hSucc]
    have lo' := mul_le_mul_of_nonneg_right lo hδ.le
    have hi' := mul_le_mul_of_nonneg_right hFloor hδ.le
    rw [sub_mul, hFlat] at lo'
    rw [add_mul, hFlat] at hi'
    exact abs_le.mpr ⟨by linarith only [lo'], by linarith only [hi']⟩
  have hClamp : |c - v| ≤ |(q : ℝ) - v| := by
    have hmin := abs_min_sub_min_le_max (1 : ℝ) (q : ℝ) 1 v
    have hmax := abs_max_sub_max_le_max (-1 : ℝ) (min 1 (q : ℝ)) (-1) (min 1 v)
    simp only [sub_self, abs_zero] at hmin hmax
    rw [max_eq_right (abs_nonneg ((q : ℝ) - v)), min_eq_right hv.2] at hmin
    rw [max_eq_right (abs_nonneg (min 1 (q : ℝ) - min 1 v)), min_eq_right hv.2,
      max_eq_right hv.1] at hmax
    exact hmax.trans hmin
  change (-1 ≤ (k : ℝ) * δ ∧ (k : ℝ) * δ ≤ 1) ∧ |(k : ℝ) * δ - v| ≤ δ
  have lo := mul_le_mul_of_nonneg_right hRealMin hδ.le
  have hi := mul_le_mul_of_nonneg_right hRealMax hδ.le
  rw [neg_mul, hCancel] at lo
  rw [hCancel] at hi
  refine ⟨⟨lo, hi⟩, ?_⟩
  calc
    |(k : ℝ) * δ - v| = |((k : ℝ) * δ - c) + (c - v)| := by congr 1 <;> ring
    _ ≤ |(k : ℝ) * δ - c| + |c - v| := abs_add_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hRound (hClamp.trans h)
    _ = δ := by ring

theorem EvaluationInput.rounded_correct (d : EvaluationInput) :
    d.output (encodeGrid d.rounded) := by
  let I := d.prepared.inst
  let L := valuationBits I
  let R : ℝ := logRadius I
  let f := I.normalizedBiasedMap L
  let x := dyadicPoint d.inputPrecision d.numerator
  let z := d.scaledPoint
  let t := d.precision + 4
  let ε := precisionError t
  let δ := precisionError d.precision
  let θ := I.bias L
  have hRow (i : I.Agent) : I.PositiveRow i := by
    obtain ⟨g, hg⟩ := d.prepared.preparation.prepared_positive_agents d.prepared.valid i
    exact ⟨g, by exact_mod_cast hg⟩
  have zCast (j : I.Agent) : (z j : ℝ) = R * x j := by
    simp [z, EvaluationInput.scaledPoint, R, I, x, dyadicPoint, precisionError, div_eq_mul_inv]
  have hZ : (fun j => (z j : ℝ)) = fun j => R * x j := funext zCast
  have hR : 1 ≤ R := by
    have h : 1 ≤ logRadius I := by unfold logRadius; omega
    dsimp only [R]
    exact_mod_cast h
  have θPos : 0 ≤ θ := by dsimp [θ, Instance.bias, Instance.precision]; positivity
  have θLe : θ ≤ 1 := by
    dsimp [θ, Instance.bias, Instance.precision]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have epsNonneg : 0 ≤ ε := by dsimp [ε, precisionError]; positivity
  have deltaNonneg : 0 ≤ δ := by dsimp [δ, precisionError]; positivity
  have shift : 16 * ε = δ := by
    dsimp [t, ε, δ, precisionError]
    rw [pow_add, mul_inv]
    norm_num
    ring
  have mappedInCube : unitCube (f x) :=
    (prepared_normalized_map_contract d.prepared).1 x d.inCube
  have rawError (i : I.Agent) : |(d.rawApproximation i : ℝ) - f x i| ≤ δ / 2 := by
    let a := (cutoffThreshold I z t i : ℝ)
    let b := I.logThresholdMap (fun j => R * x j) i
    let c := (guardedLog 4 t : ℝ)
    let cap := Real.log 4
    have hA : |a - b| ≤ 3 * ε := by
      have h := cutoffThreshold_error I z t i (hRow i)
      rwa [hZ] at h
    have hC : |c - cap| ≤ ε := guardedLog_error 4 t (by norm_num)
    have rawCast : (d.rawApproximation i : ℝ) = ((1 - θ) * a + θ * c) / R := by
      simp only [EvaluationInput.rawApproximation, Rat.cast_div, Rat.cast_add, Rat.cast_mul,
        Rat.cast_sub, Rat.cast_one, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast]
      rfl
    change |(d.rawApproximation i : ℝ) - ((1 - θ) * b + θ * cap) / R| ≤ δ / 2
    rw [rawCast, ← sub_div, abs_div, abs_of_nonneg (show 0 ≤ R by linarith)]
    have join : (1 - θ) * a + θ * c - ((1 - θ) * b + θ * cap) =
        (1 - θ) * (a - b) + θ * (c - cap) := by ring
    rw [join]
    calc
      _ ≤ (|(1 - θ) * (a - b)| + |θ * (c - cap)|) / R :=
        div_le_div_of_nonneg_right (abs_add_le _ _) (by linarith)
      _ = ((1 - θ) * |a - b| + θ * |c - cap|) / R := by
        rw [abs_mul, abs_mul, abs_of_nonneg θPos, abs_of_nonneg (sub_nonneg.mpr θLe)]
      _ ≤ ((1 - θ) * (3 * ε) + θ * (3 * ε)) / R :=
        div_le_div_of_nonneg_right (add_le_add
          (mul_le_mul_of_nonneg_left hA (sub_nonneg.mpr θLe))
          (mul_le_mul_of_nonneg_left (hC.trans (by linarith only [epsNonneg])) θPos)) (by linarith)
      _ = 3 * ε / R := by ring
      _ ≤ 3 * ε := div_le_self (by positivity) hR
      _ ≤ δ / 2 := by linarith only [epsNonneg, shift]
  have rounded (i : I.Agent) := roundedNumerator_error d.precision (d.rawApproximation i)
    (f x i) (mappedInCube i) (rawError i)
  refine ⟨d.rounded, fun i => (rounded i).1, ?_, rfl⟩
  apply (dist_pi_le_iff deltaNonneg).mpr
  intro i
  change dist ((roundedNumerator d.precision (d.rawApproximation i) : ℝ) * δ) (f x i) ≤ δ
  simpa only [Real.dist_eq] using (rounded i).2

end

end EF1FPO
