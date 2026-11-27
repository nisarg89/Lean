import EF1FPO.Weights
import EF1FPO.RationalBounds
import EF1FPO.DirectedPaths

/-! Logarithmic coordinates, perturbation of the fixed point, and exact tie recovery. -/

set_option autoImplicit false

open scoped BigOperators

namespace EF1FPO.Instance

variable (I : Instance)

/-- Input numerator and denominator bounds, with each input rational reduced. -/
def RatHeight (L : ℕ) : Prop :=
  ∀ i g, (I.v i g).num.natAbs ≤ 2 ^ L ∧ (I.v i g).den ≤ 2 ^ L

def LogInputBound (L : ℕ) : Prop :=
  4 ≤ L ∧ I.n + I.m ≤ L ∧ I.RatHeight L

def PositiveColumns : Prop := ∀ g, ∃ i, 0 < I.value i g

def P (L : ℕ) : ℕ := 16 * (I.n + I.m + 1) * (L + 1)

def R (_I : Instance) (L : ℕ) : ℕ := 4 * (L + 1)

noncomputable def logWeights (w : I.Weights) : I.Weights := fun i => Real.log (w i)

noncomputable def expWeights (x : I.Weights) : I.Weights := fun i => Real.exp (x i)

noncomputable def logCap : I.Weights := I.logWeights I.cap

def cube (r : ℝ) : Set I.Weights := {x | ∀ i, |x i| ≤ r}

noncomputable def logThresholdMap (x : I.Weights) : I.Weights :=
  fun i => min (I.logCap i) (Real.log (I.threshold (I.expWeights x) i))

/-- `2⁻ᵏ` for a natural precision parameter. -/
noncomputable def precision (k : ℕ) : ℝ := ((2 : ℝ) ^ k)⁻¹

noncomputable def bias (L : ℕ) : ℝ := precision (16 * I.P L)

noncomputable def biasedMap (L : ℕ) (x : I.Weights) : I.Weights :=
  fun i => (1 - I.bias L) * I.logThresholdMap x i + I.bias L * I.logCap i

noncomputable def normalizedBiasedMap (L : ℕ) (x : I.Weights) : I.Weights :=
  fun i => (I.biasedMap L (fun j => (I.R L : ℝ) * x j) i) / (I.R L : ℝ)

noncomputable def repairSlack (L : ℕ) : ℝ := 2 * (I.R L : ℝ) * I.bias L

theorem logMap_postfixed_iff (x : I.Weights) (hrow : ∀ i, I.PositiveRow i) :
    x ≤ I.logThresholdMap x ↔ I.IsFeasible I.cap (I.expWeights x) := by
  have hw : I.Positive (I.expWeights x) := fun i => Real.exp_pos (x i)
  have hcap (i : I.Agent) : 0 < I.cap i := by norm_num [cap]
  have hb (i : I.Agent) : 0 < I.threshold (I.expWeights x) i :=
    I.threshold_pos (I.expWeights x) i (hrow i)
  constructor
  · intro hx
    refine ⟨hw, fun i => ?_, fun i => ?_⟩
    · exact (Real.le_log_iff_exp_le (hcap i)).1 ((le_min_iff.mp (hx i)).1)
    · exact (I.forced_spending_le_one_iff _ i hw (hrow i)).2
        ((Real.le_log_iff_exp_le (hb i)).1 ((le_min_iff.mp (hx i)).2))
  · intro hf i
    apply le_min
    · exact (Real.le_log_iff_exp_le (hcap i)).2 (hf.2.1 i)
    · exact (Real.le_log_iff_exp_le (hb i)).2
        ((I.forced_spending_le_one_iff _ i hw (hrow i)).1 (hf.2.2 i))

theorem logMap_monotone : Monotone I.logThresholdMap := by
  intro x y hxy i
  unfold logThresholdMap
  apply min_le_min le_rfl
  have he : I.expWeights x ≤ I.expWeights y := fun j => Real.exp_le_exp.mpr (hxy j)
  by_cases hi : I.PositiveRow i
  · exact Real.log_le_log (I.threshold_pos (I.expWeights x) i hi)
      (I.threshold_monotone i he)
  · have hne : ¬ (I.positiveBundles i).Nonempty := by
      rintro ⟨S, hS⟩
      obtain ⟨hneS, hsub⟩ := Finset.mem_erase.mp hS
      obtain ⟨g, hg⟩ := Finset.nonempty_iff_ne_empty.mpr hneS
      have hpos := Finset.mem_powerset.mp hsub hg
      exact hi ⟨g, by simpa [positiveGoods] using hpos⟩
    simp [threshold, hne]

theorem logMap_nonexpansive (hrow : ∀ i, I.PositiveRow i) :
    LipschitzWith 1 I.logThresholdMap := by
  classical
  have oneSided (x y : I.Weights) (d : ℝ) (hd : 0 ≤ d)
      (hxy : ∀ j, x j ≤ y j + d) (i : I.Agent) :
      I.logThresholdMap x i ≤ I.logThresholdMap y i + d := by
    let c := Real.exp d
    have hc : 0 < c := Real.exp_pos _
    have hc1 : 1 ≤ c := by simpa [c] using Real.exp_le_exp.mpr hd
    let wx := I.expWeights x
    let wy := I.expWeights y
    have hw (j : I.Agent) : wx j ≤ c * wy j := by
      change Real.exp (x j) ≤ Real.exp d * Real.exp (y j)
      rw [← Real.exp_add, add_comm d]
      exact Real.exp_le_exp.mpr (hxy j)
    have hR (g : I.Good) : I.rivalThreshold wx i g ≤ c * I.rivalThreshold wy i g := by
      unfold rivalThreshold
      refine Finset.sup'_le _ _ (fun j _ => ?_)
      have hterm : (if j = i then 0 else I.bid wx j g / I.value i g) ≤
          c * (if j = i then 0 else I.bid wy j g / I.value i g) := by
        by_cases hji : j = i
        · simp [hji]
        · simp only [hji, ite_false]
          have hvj : 0 ≤ I.value j g := by exact_mod_cast I.nonneg j g
          have hvi : 0 ≤ I.value i g := by exact_mod_cast I.nonneg i g
          have hb : I.bid wx j g ≤ c * I.bid wy j g := by
            simpa only [bid, mul_assoc] using mul_le_mul_of_nonneg_right (hw j) hvj
          rw [← mul_div_assoc]
          exact div_le_div_of_nonneg_right hb hvi
      exact hterm.trans (mul_le_mul_of_nonneg_left
        (Finset.le_sup' (fun j => if j = i then 0 else I.bid wy j g / I.value i g)
          (Finset.mem_univ j)) hc.le)
    obtain ⟨g, hg⟩ := hrow i
    have hg' : g ∈ I.positiveGoods i := by
      simp [positiveGoods]
      exact_mod_cast hg
    have hne : (I.positiveBundles i).Nonempty := by
      refine ⟨{g}, Finset.mem_erase.mpr ⟨Finset.singleton_ne_empty _, ?_⟩⟩
      exact Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hg')
    let term (w : I.Weights) (S : Finset I.Good) : ℝ :=
      max (I.utility i S)⁻¹ (if hS : S.Nonempty then S.sup' hS (I.rivalThreshold w i) else 0)
    obtain ⟨S, hs, hsy⟩ := Finset.exists_mem_eq_inf' hne (term wy)
    have hyTerm : I.threshold wy i = term wy S := by rw [threshold, dite_eq_left hne]; exact hsy
    have hxTerm : I.threshold wx i ≤ term wx S := by
      rw [threshold, dite_eq_left hne]
      exact Finset.inf'_le (term wx) hs
    obtain ⟨hSnonempty, hSsub⟩ := Finset.mem_erase.mp hs
    have hS := Finset.nonempty_iff_ne_empty.mpr hSnonempty
    have hU : 0 < I.utility i S := by
      apply Finset.sum_pos _ hS
      intro f hf
      have hgood := Finset.mem_powerset.mp hSsub hf
      simpa [positiveGoods] using hgood
    have termScaled : term wx S ≤ c * term wy S := by
      simp only [term, dite_eq_left hS]
      apply max_le
      · have h := mul_le_mul_of_nonneg_right hc1 (inv_nonneg.mpr hU.le)
        rw [one_mul] at h
        exact h.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hc.le)
      · refine Finset.sup'_le _ _ (fun f hf => ?_)
        exact (hR f).trans (mul_le_mul_of_nonneg_left
          ((Finset.le_sup' (I.rivalThreshold wy i) hf).trans (le_max_right _ _)) hc.le)
    have hthreshold : I.threshold wx i ≤ c * I.threshold wy i := by
      rw [hyTerm]
      exact hxTerm.trans termScaled
    have logBound := Real.log_le_log (I.threshold_pos wx i (hrow i)) hthreshold
    rw [Real.log_mul hc.ne' (I.threshold_pos wy i (hrow i)).ne'] at logBound
    change Real.log (I.threshold wx i) ≤ Real.log (Real.exp d) + Real.log (I.threshold wy i)
      at logBound
    rw [Real.log_exp, add_comm d] at logBound
    change min (I.logCap i) (Real.log (I.threshold wx i)) ≤
      min (I.logCap i) (Real.log (I.threshold wy i)) + d
    rw [← min_add_add_right]
    exact min_le_min (by linarith) logBound
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul]
  refine (dist_pi_le_iff dist_nonneg).2 (fun i => ?_)
  rw [Real.dist_eq]
  have hxy (j : I.Agent) : x j ≤ y j + dist x y := by
    have h := dist_le_pi_dist x y j
    rw [Real.dist_eq] at h
    linarith [(abs_le.mp h).2]
  have hyx (j : I.Agent) : y j ≤ x j + dist x y := by
    have h := dist_le_pi_dist x y j
    rw [Real.dist_eq] at h
    linarith [(abs_le.mp h).1]
  have hupper := oneSided x y (dist x y) dist_nonneg hxy i
  have hlower := oneSided y x (dist x y) dist_nonneg hyx i
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem logMap_mem_cube (L : ℕ) (hL : I.LogInputBound L) (hrow : ∀ i, I.PositiveRow i)
    (x : I.Weights) : I.logThresholdMap x ∈ I.cube (I.R L) := by
  classical
  intro i
  obtain ⟨g, hg⟩ := hrow i
  have hm : (0 : ℝ) < I.m := by exact_mod_cast Nat.zero_lt_of_lt g.isLt
  have hmL : (I.m : ℝ) ≤ L := by exact_mod_cast (show I.m ≤ L by have := hL.2.1; omega)
  let T : ℝ := I.m * (2 : ℝ) ^ L
  have hT : 0 < T := mul_pos hm (by positivity)
  have hlogT : Real.log T ≤ 2 * (L : ℝ) := by
    unfold T
    rw [Real.log_mul hm.ne' (by positivity), Real.log_pow]
    have hmLog := Real.log_le_sub_one_of_pos hm
    have h2Log := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    have hpowLog := mul_le_mul_of_nonneg_left h2Log (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    linarith
  have hvalue (f : I.Good) : I.value i f ≤ (2 : ℝ) ^ L := by
    let q := I.v i f
    have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr (I.nonneg i f)
    have hnumEq : (q.num : ℝ) = (q.num.natAbs : ℝ) := by
      simpa only [Int.cast_natCast] using
        congrArg (fun z : ℤ => (z : ℝ)) (Int.natAbs_of_nonneg hnum).symm
    have hden : (1 : ℝ) ≤ q.den := by exact_mod_cast Nat.one_le_of_lt (Rat.den_pos q)
    have hnumBound : (q.num.natAbs : ℝ) ≤ (2 : ℝ) ^ L := by exact_mod_cast (hL.2.2 i f).1
    change (q : ℝ) ≤ _
    rw [Rat.cast_def, hnumEq]
    exact (div_le_self (Nat.cast_nonneg _) hden).trans hnumBound
  have hbound (S : Finset I.Good) : I.utility i S ≤ T := by
    have hcard : S.card ≤ I.m := by
      simpa using Finset.card_le_card (Finset.subset_univ S)
    unfold T
    calc
      _ ≤ ∑ f ∈ S, (2 : ℝ) ^ L := Finset.sum_le_sum (fun f _ => hvalue f)
      _ = (S.card : ℝ) * (2 : ℝ) ^ L := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  have hg' : g ∈ I.positiveGoods i := by
    simp [positiveGoods]
    exact_mod_cast hg
  have hne : (I.positiveBundles i).Nonempty := by
    refine ⟨{g}, Finset.mem_erase.mpr ⟨Finset.singleton_ne_empty _, ?_⟩⟩
    exact Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hg')
  have hthreshold : T⁻¹ ≤ I.threshold (I.expWeights x) i := by
    rw [threshold, dite_eq_left hne]
    apply Finset.le_inf' _ _
    intro S hS
    obtain ⟨hSnonempty, hSsub⟩ := Finset.mem_erase.mp hS
    have hSpos : 0 < I.utility i S := by
      apply Finset.sum_pos _ (Finset.nonempty_iff_ne_empty.mpr hSnonempty)
      intro f hf
      have hgood := Finset.mem_powerset.mp hSsub hf
      simpa [positiveGoods] using hgood
    exact (inv_anti₀ hSpos (hbound S)).trans (le_max_left _ _)
  have hlog := Real.log_le_log (inv_pos.mpr hT) hthreshold
  rw [Real.log_inv] at hlog
  have hRad : 2 * (L : ℝ) + 4 ≤ (I.R L : ℝ) := by
    simp [R]
    linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hcapPos : 0 ≤ Real.log 4 := (Real.log_pos (by norm_num : (1 : ℝ) < 4)).le
  have hcapBound := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
  change |min (Real.log 4) (Real.log (I.threshold (I.expWeights x) i))| ≤ (I.R L : ℝ)
  apply abs_le.mpr
  exact ⟨le_min (by linarith) (by linarith), (min_le_left _ _).trans (by linarith)⟩

theorem biased_map_contraction (L : ℕ) (hrow : ∀ i, I.PositiveRow i) :
    ContractingWith (Real.toNNReal (1 - I.bias L)) (I.biasedMap L) := by
  have hθ : 0 < I.bias L := by unfold bias precision; positivity
  have hθle : I.bias L ≤ 1 := by
    have h : (1 : ℝ) ≤ (2 : ℝ) ^ (16 * I.P L) := one_le_pow₀ (by norm_num)
    simpa only [bias, precision, inv_one] using inv_anti₀ zero_lt_one h
  have hc : 0 ≤ 1 - I.bias L := sub_nonneg.mpr hθle
  constructor
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hc, NNReal.coe_one]
    linarith
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.coe_toNNReal _ hc]
    refine (dist_pi_le_iff (mul_nonneg hc dist_nonneg)).2 (fun i => ?_)
    have hF := (I.logMap_nonexpansive hrow).dist_le_mul x y
    rw [NNReal.coe_one, one_mul] at hF
    have hi := (dist_le_pi_dist (I.logThresholdMap x) (I.logThresholdMap y) i).trans hF
    have hscale : I.biasedMap L x i - I.biasedMap L y i =
        (1 - I.bias L) * (I.logThresholdMap x i - I.logThresholdMap y i) := by
      simp only [biasedMap]
      ring
    rw [Real.dist_eq, hscale, abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.dist_eq] using hi) hc

theorem normalized_biased_map_contraction (L : ℕ) (hrow : ∀ i, I.PositiveRow i) :
    ContractingWith (Real.toNNReal (1 - I.bias L)) (I.normalizedBiasedMap L) := by
  let r : ℝ := I.R L
  have hr : 0 < r := by dsimp [r, R]; positivity
  let k := Real.toNNReal (1 - I.bias L)
  have hH : ContractingWith k (I.biasedMap L) := I.biased_map_contraction L hrow
  refine ⟨hH.1, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  have hnorm (t : ℝ) (ht : 0 < t) (v u : I.Weights) :
      dist (t • v) (t • u) = t * dist v u := by
    simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have heq (x : I.Weights) :
      I.normalizedBiasedMap L x = r⁻¹ • I.biasedMap L (r • x) := by
    funext i
    change I.biasedMap L (r • x) i / r = r⁻¹ * I.biasedMap L (r • x) i
    rw [div_eq_mul_inv, mul_comm]
  rw [heq x, heq y, hnorm r⁻¹ (inv_pos.mpr hr)]
  calc
    _ ≤ r⁻¹ * ((k : ℝ) * dist (r • x) (r • y)) :=
      mul_le_mul_of_nonneg_left (hH.dist_le_mul _ _) (inv_nonneg.mpr hr.le)
    _ = (k : ℝ) * dist x y := by rw [hnorm r hr]; field_simp [hr.ne']

theorem normalized_biased_map_cube (L : ℕ) (hL : I.LogInputBound L)
    (hrow : ∀ i, I.PositiveRow i) :
    Set.MapsTo (I.normalizedBiasedMap L) (I.cube 1) (I.cube 1) := by
  intro x _ i
  have hRfour : (4 : ℝ) ≤ I.R L := by
    rw [R]
    push_cast
    linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hR : (0 : ℝ) < I.R L := by linarith
  have hθ : 0 ≤ I.bias L := by unfold bias precision; positivity
  have hθle : I.bias L ≤ 1 := by
    have h : (1 : ℝ) ≤ (2 : ℝ) ^ (16 * I.P L) := one_le_pow₀ (by norm_num)
    simpa only [bias, precision, inv_one] using inv_anti₀ zero_lt_one h
  have hC : |I.logCap i| ≤ (I.R L : ℝ) := by
    change |Real.log 4| ≤ (I.R L : ℝ)
    have h4 : (1 : ℝ) < 4 := by norm_num
    rw [abs_of_pos (Real.log_pos h4)]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
  let z : I.Weights := fun j => (I.R L : ℝ) * x j
  have hF : |I.logThresholdMap z i| ≤ (I.R L : ℝ) := I.logMap_mem_cube L hL hrow z i
  have hH : |I.biasedMap L z i| ≤ (I.R L : ℝ) := by
    unfold biasedMap
    calc
      _ ≤ |(1 - I.bias L) * I.logThresholdMap z i| + |I.bias L * I.logCap i| := abs_add_le _ _
      _ ≤ (1 - I.bias L) * (I.R L : ℝ) + I.bias L * (I.R L : ℝ) := by
        simp only [abs_mul, abs_of_nonneg hθ, abs_of_nonneg (sub_nonneg.mpr hθle)]
        exact add_le_add (mul_le_mul_of_nonneg_left hF (sub_nonneg.mpr hθle))
          (mul_le_mul_of_nonneg_left hC hθ)
      _ = (I.R L : ℝ) := by ring
  change |I.biasedMap L z i / (I.R L : ℝ)| ≤ 1
  rw [abs_div, abs_of_pos hR, div_le_one hR]
  exact hH

theorem biased_fixed_point (L : ℕ) (hL : I.LogInputBound L) (hrow : ∀ i, I.PositiveRow i) :
    ∃! z : I.Weights, z ∈ I.cube (I.R L) ∧ I.biasedMap L z = z := by
  let r : ℝ := I.R L
  have hr : 0 < r := by dsimp [r, R]; positivity
  have hClosed : IsClosed (I.cube r) := by
    rw [cube, Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_le ((continuous_apply i).abs) continuous_const)
  have hmap : Set.MapsTo (I.biasedMap L) (I.cube r) (I.cube r) := by
    intro x hx
    let y : I.Weights := fun i => x i / r
    have hy : y ∈ I.cube 1 := fun i => by
      change |x i / r| ≤ 1
      rw [abs_div, abs_of_pos hr, div_le_one hr]
      exact hx i
    have hnorm := I.normalized_biased_map_cube L hL hrow hy
    have hscale : (fun j => r * y j) = x := by
      funext i
      change r * (x i / r) = x i
      field_simp [hr.ne']
    intro i
    have hi := hnorm i
    change |I.biasedMap L (fun j => r * y j) i / r| ≤ 1 at hi
    rwa [hscale, abs_div, abs_of_pos hr, div_le_one hr] at hi
  have hzero : (0 : I.Weights) ∈ I.cube r := fun _ => by simpa using hr.le
  have hcon := I.biased_map_contraction L hrow
  obtain ⟨z, hz, hfix, _, _⟩ := ContractingWith.exists_fixedPoint' hClosed.isComplete
    hmap (hcon.restrict hmap) hzero (edist_ne_top _ _)
  exact ⟨z, ⟨hz, hfix⟩, fun _ h => hcon.fixedPoint_unique' h.2 hfix⟩

set_option maxHeartbeats 4000000 in
/-- Choose maximizing terms in the finite subset formula and repair the
selected difference inequalities by taking shortest paths. -/
theorem repair_approx_postfixed (L : ℕ) (hL : I.LogInputBound L)
    (hrow : ∀ i, I.PositiveRow i) (z : I.Weights) (hcap : z ≤ I.logCap)
    (happrox : ∀ i, z i ≤ I.logThresholdMap z i + I.repairSlack L) :
    ∃ x : I.Weights, x ≤ I.logThresholdMap x ∧
      ∀ i, z i - (I.n : ℝ) * I.repairSlack L ≤ x i ∧ x i ≤ z i := by
  classical
  let ε := I.repairSlack L
  have hε : 0 ≤ ε := by dsimp [ε, repairSlack, bias, precision]; positivity
  let v := Option I.Agent
  let z' (a : v) : ℝ := a.elim 0 z
  let ratio (i j : I.Agent) (g : I.Good) : ℝ := I.value j g / I.value i g
  let arrow : v → v → Type
    | none, _ => PEmpty
    | some i, none => {c : ℝ // z i ≤ c + ε}
    | some i, some j => {g : I.Good // 0 < I.value i g ∧ 0 < I.value j g ∧
        z i ≤ Real.log (ratio i j g) + z j + ε}
  letI : Quiver v := ⟨arrow⟩
  let cost : ∀ {a b : v}, (a ⟶ b) → ℝ
    | none, _, e => PEmpty.elim e
    | some _, none, e => e.val
    | some i, some j, e => Real.log (ratio i j e.val)
  have no_edge_none {b : v} (e : (none : v) ⟶ b) : False := PEmpty.elim e
  have edge_approx {a b : v} (e : a ⟶ b) : z' a ≤ cost e + z' b + ε := by
    cases a with
    | none => exact (no_edge_none e).elim
    | some i =>
      cases b with
      | none =>
        change z i ≤ e.val + 0 + ε
        simpa only [add_zero] using e.property
      | some j => exact e.property.2.2
  have path_approx {a b : v} (p : Quiver.Path a b) :
      z' a ≤ p.addWeight cost + z' b + (p.length : ℝ) * ε := by
    induction p with
    | nil => simp
    | @cons b c p e ih =>
      have he := edge_approx e
      simp only [Quiver.Path.addWeight_cons, Quiver.Path.length_cons, Nat.cast_succ]
      linarith
  have edge_ratio {a b : v} (e : a ⟶ b) (hb : b ≠ none) : a ≠ none ∧
      RationalBounds.PositiveRatio (2 ^ (2 * L)) (Real.exp (cost e)) := by
    cases a with
    | none => exact (no_edge_none e).elim
    | some i =>
      cases b with
      | none => exact (hb rfl).elim
      | some j =>
        refine ⟨Option.some_ne_none _, ?_⟩
        obtain ⟨hi, hj, _⟩ := e.property
        change RationalBounds.PositiveRatio _ (Real.exp (Real.log (I.value j e.val / I.value i e.val)))
        rw [Real.exp_log (div_pos hj hi), div_eq_mul_inv, two_mul, pow_add]
        exact RationalBounds.mul_ratio
          (RationalBounds.of_rat _ (I.v j e.val) (by exact_mod_cast hj)
            (hL.2.2 j e.val).1 (hL.2.2 j e.val).2)
          (RationalBounds.inv_ratio (RationalBounds.of_rat _ (I.v i e.val) (by exact_mod_cast hi)
            (hL.2.2 i e.val).1 (hL.2.2 i e.val).2))
  have path_ratio {a b : v} (p : Quiver.Path a b) : b ≠ none →
      RationalBounds.PositiveRatio (2 ^ ((2 * L) * p.length)) (Real.exp (p.addWeight cost)) := by
    induction p with
    | nil =>
      intro _
      simp only [Quiver.Path.length_nil, mul_zero, pow_zero, Quiver.Path.addWeight_nil, Real.exp_zero]
      exact ⟨1, 1, by decide, by decide, le_rfl, le_rfl, by norm_num⟩
    | @cons b c p e ih =>
      intro hc
      obtain ⟨hb, he⟩ := edge_ratio e hc
      rw [Quiver.Path.addWeight_cons, Real.exp_add, Quiver.Path.length_cons, Nat.mul_succ, pow_add]
      exact RationalBounds.mul_ratio (ih hb) he
  have vertices_agents {a b : v} (p : Quiver.Path a b) : b ≠ none →
      ∀ x ∈ p.vertices, x ≠ none := by
    induction p with
    | nil => simp
    | @cons b c p e ih =>
      intro hc x hx
      obtain hm | rfl := (Quiver.Path.mem_vertices_cons p e).mp hx
      · exact ih (edge_ratio e hc).1 x hm
      · exact hc
  let H := 2 * L * I.n
  have hH : H ≤ I.P L := by
    unfold H P
    calc
      2 * L * I.n = (2 * I.n) * L := by ring
      _ ≤ _ := Nat.mul_le_mul (by omega) (Nat.le_succ L)
  have hNum : 2 * I.n * I.R L ≤ I.P L := by
    unfold R P
    calc
      2 * I.n * (4 * (L + 1)) = (8 * I.n) * (L + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have hSlack : (I.n : ℝ) * ε < precision H := by
    let M := 16 * I.P L - H
    have hM : I.P L ≤ M := by dsimp [M]; omega
    have hSum : 16 * I.P L = M + H := by dsimp [M]; omega
    have hNat : 2 * I.n * I.R L < (2 : ℕ) ^ I.P L :=
      hNum.trans_lt Nat.lt_two_pow_self
    have hReal : 2 * (I.n : ℝ) * (I.R L : ℝ) < (2 : ℝ) ^ I.P L := by exact_mod_cast hNat
    have hb : 0 < precision (16 * I.P L) := by unfold precision; positivity
    have hCoef : (2 : ℝ) ^ I.P L * ((2 : ℝ) ^ M)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by positivity)]
      exact pow_le_pow_right₀ (by norm_num) hM
    calc
      _ = (2 * (I.n : ℝ) * (I.R L : ℝ)) * precision (16 * I.P L) := by
        dsimp [ε, repairSlack, bias]; ring
      _ < (2 : ℝ) ^ I.P L * precision (16 * I.P L) := mul_lt_mul_of_pos_right hReal hb
      _ ≤ precision H := by
        rw [hSum]
        unfold precision
        rw [pow_add (2 : ℝ) M H, mul_inv, ← mul_assoc]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hCoef (by positivity :
          0 ≤ ((2 : ℝ) ^ H)⁻¹)
  have cycle_nonneg {a b : v} (p : Quiver.Path a b) (e : b ⟶ a)
      (hp : p.vertices.Nodup) : 0 ≤ (p.cons e).addWeight cost := by
    have hb : b ≠ none := by
      rintro rfl
      exact no_edge_none e
    have ha : a ≠ none := vertices_agents p hb a p.start_mem_vertices
    have hsub : p.vertices.toFinset ⊆ (Finset.univ.erase none : Finset v) := by
      intro a ha
      exact Finset.mem_erase.mpr ⟨vertices_agents p hb a (List.mem_toFinset.mp ha), Finset.mem_univ a⟩
    have hn := Finset.card_mono hsub
    have hlen : (p.cons e).length ≤ I.n := by
      rw [List.toFinset_card_of_nodup hp, Quiver.Path.vertices_length] at hn
      simpa [v, Quiver.Path.length_cons, Finset.card_erase_of_mem] using hn
    have hLenReal : ((p.cons e).length : ℝ) ≤ I.n := by exact_mod_cast hlen
    have hratio := RationalBounds.mono_ratio (path_ratio (p.cons e) ha)
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left (2 * L) hlen))
    by_contra hn
    have hlt : Real.exp ((p.cons e).addWeight cost) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (lt_of_not_ge hn)
    have hLog := RationalBounds.log_le_negative_inv hratio hlt
    rw [Real.log_exp] at hLog
    have hCost : (p.cons e).addWeight cost ≤ -precision H := by
      simpa [precision, H] using hLog
    have hApprox := path_approx (p.cons e)
    linarith [mul_le_mul_of_nonneg_right hLenReal hε]
  let costMult : ∀ {a b : v}, (a ⟶ b) → Multiplicative ℝ := fun e =>
    Multiplicative.ofAdd (cost e)
  have multWeight {a b : v} (p : Quiver.Path a b) :
      p.weight costMult = Multiplicative.ofAdd (p.addWeight cost) := by
    induction p with
    | nil => simp only [Quiver.Path.weight_nil, Quiver.Path.addWeight_nil, ofAdd_zero]
    | cons p e ih => simp only [Quiver.Path.weight_cons, Quiver.Path.addWeight_cons, ih,
        costMult, ofAdd_add]
  have short {a b : v} (p : Quiver.Path a b) :
      ∃ q : Quiver.Path a b, q.vertices.Nodup ∧ q.addWeight cost ≤ p.addWeight cost := by
    have left_mono (x : Multiplicative ℝ) : Monotone (x * ·) := by
      intro y z hyz
      change Multiplicative.toAdd x + Multiplicative.toAdd y ≤
        Multiplicative.toAdd x + Multiplicative.toAdd z
      exact add_le_add le_rfl hyz
    have right_mono (x : Multiplicative ℝ) : Monotone (· * x) := by
      intro y z hyz
      change Multiplicative.toAdd y + Multiplicative.toAdd x ≤
        Multiplicative.toAdd z + Multiplicative.toAdd x
      exact add_le_add hyz le_rfl
    obtain ⟨q, hq, hqp⟩ := DirectedPaths.exists_nodup_path_weight_le costMult left_mono right_mono
      (fun q e h => by rw [multWeight]; exact cycle_nonneg q e h) p
    rw [multWeight, multWeight] at hqp
    exact ⟨q, hq, hqp⟩
  let values (a : v) : Set ℝ := {t | ∃ b, ∃ p : Quiver.Path a b,
    t = p.addWeight cost + z' b}
  have zero_path (a : v) : z' a ∈ values a := ⟨a, Quiver.Path.nil, by simp⟩
  have nonempty (a : v) : (values a).Nonempty := ⟨z' a, zero_path a⟩
  have lower (a : v) (t : ℝ) (ht : t ∈ values a) : z' a - (I.n : ℝ) * ε ≤ t := by
    obtain ⟨b, p, rfl⟩ := ht
    obtain ⟨q, hq, hLE⟩ := short p
    have hLen : q.length ≤ I.n := by
      have hCard := hq.length_le_card
      simp [Quiver.Path.vertices_length, v] at hCard
      omega
    have hLenR : (q.length : ℝ) ≤ I.n := by exact_mod_cast hLen
    linarith [path_approx q, mul_le_mul_of_nonneg_right hLenR hε]
  have bdd (a : v) : BddBelow (values a) := ⟨z' a - (I.n : ℝ) * ε, fun _ ht => lower a _ ht⟩
  let pot (a : v) : ℝ := sInf (values a)
  have pot_lo (a : v) : z' a - (I.n : ℝ) * ε ≤ pot a :=
    le_csInf (nonempty a) (lower a)
  have pot_hi (a : v) : pot a ≤ z' a := csInf_le (bdd a) (zero_path a)
  have none_nil {a b : v} (p : Quiver.Path a b) : a = none → p.length = 0 ∧ b = none := by
    induction p with
    | nil => simp
    | @cons b c p e ih =>
      intro ha
      obtain ⟨_, rfl⟩ := ih ha
      exact (no_edge_none e).elim
  have pot_none : pot none = 0 := by
    refine le_antisymm (pot_hi none) (le_csInf (nonempty none) ?_)
    intro t ht
    obtain ⟨b, p, rfl⟩ := ht
    obtain ⟨hlen, rfl⟩ := none_nil p rfl
    have heq := (Quiver.Path.length_eq_zero_iff p).mp hlen
    rw [heq]
    simp [z']
  have exact_edge {a b : v} (e : a ⟶ b) : pot a ≤ cost e + pot b := by
    have hle : pot a - cost e ≤ pot b := by
      refine le_csInf (nonempty b) (fun t ht => ?_)
      obtain ⟨c, p, rfl⟩ := ht
      have hmem : cost e + (p.addWeight cost + z' c) ∈ values a := by
        refine ⟨c, e.toPath.comp p, ?_⟩
        simp [Quiver.Hom.toPath, add_assoc]
      linarith [csInf_le (bdd a) hmem]
    linarith
  let x : I.Weights := fun i => pot (some i)
  refine ⟨x, ?_, fun i => ⟨pot_lo (some i), pot_hi (some i)⟩⟩
  intro i
  change x i ≤ min (I.logCap i) (Real.log (I.threshold (I.expWeights x) i))
  apply le_min ((pot_hi (some i)).trans (hcap i))
  apply (Real.le_log_iff_exp_le (I.threshold_pos (I.expWeights x) i (hrow i))).mpr
  obtain ⟨g₀, hg₀⟩ := hrow i
  have hg' : g₀ ∈ I.positiveGoods i := by simp [positiveGoods]; exact_mod_cast hg₀
  have hne : (I.positiveBundles i).Nonempty := by
    refine ⟨{g₀}, Finset.mem_erase.mpr ⟨Finset.singleton_ne_empty _, ?_⟩⟩
    exact Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hg')
  let term (u : I.Weights) (S : Finset I.Good) : ℝ :=
    max (I.utility i S)⁻¹ (if hS : S.Nonempty then
      S.sup' hS (I.rivalThreshold (I.expWeights u) i) else 0)
  rw [threshold, dite_eq_left hne]
  refine Finset.le_inf' hne (term x) (fun S hs => ?_)
  obtain ⟨hn, hsub⟩ := Finset.mem_erase.mp hs
  have hS := Finset.nonempty_iff_ne_empty.mpr hn
  have hVal (g : I.Good) (hg : g ∈ S) : 0 < I.value i g := by
    have hg' := Finset.mem_powerset.mp hsub hg
    simpa [positiveGoods] using hg'
  have hInv : 0 < (I.utility i S)⁻¹ := inv_pos.mpr (Finset.sum_pos hVal hS)
  have hzTerm : I.threshold (I.expWeights z) i ≤ term z S := by
    rw [threshold, dite_eq_left hne]
    exact Finset.inf'_le (term z) hs
  have hUpper : z i ≤ Real.log (term z S) + ε := by
    refine (happrox i).trans (add_le_add ?_ le_rfl)
    exact (min_le_right _ _).trans (Real.log_le_log
      (I.threshold_pos (I.expWeights z) i (hrow i)) hzTerm)
  let b := (I.utility i S)⁻¹
  let r := S.sup' hS (I.rivalThreshold (I.expWeights z) i)
  have term_eq (u : I.Weights) :
      term u S = max b (S.sup' hS (I.rivalThreshold (I.expWeights u) i)) := by
    simp only [term, b, dite_eq_left hS]
  by_cases hconst : r ≤ b
  · have hLinear : z i ≤ Real.log b + ε := by
      rwa [term_eq, max_eq_left hconst] at hUpper
    let e : (some i : v) ⟶ none := ⟨Real.log b, hLinear⟩
    have he := exact_edge e
    change x i ≤ Real.log b + pot none at he
    rw [pot_none, add_zero] at he
    rw [term_eq]
    exact ((Real.le_log_iff_exp_le hInv).mp he).trans (le_max_left _ _)
  · have br : b < r := lt_of_not_ge hconst
    obtain ⟨g, hg, hgEq⟩ := Finset.exists_mem_eq_sup' hS (I.rivalThreshold (I.expWeights z) i)
    have hr : 0 < I.rivalThreshold (I.expWeights z) i g := by
      rw [← hgEq]
      exact hInv.trans br
    let rf (u : I.Weights) (j : I.Agent) : ℝ :=
      if j = i then 0 else I.bid (I.expWeights u) j g / I.value i g
    have hu : (Finset.univ : Finset I.Agent).Nonempty := ⟨i, Finset.mem_univ i⟩
    obtain ⟨j, _, hjEq⟩ := Finset.exists_mem_eq_sup' hu (rf z)
    have hj' : I.rivalThreshold (I.expWeights z) i g = rf z j := hjEq
    have hji : j ≠ i := by
      intro hji
      rw [hj'] at hr
      simp only [rf, hji, ite_true] at hr
      exact (lt_irrefl _) hr
    have hEntry (u : I.Weights) : rf u j = Real.exp (u j) * ratio i j g := by
      simp only [rf, hji, ite_false, Instance.bid, expWeights, ratio, mul_div_assoc]
    have hRatio : 0 < ratio i j g := by
      rw [hj', hEntry z] at hr
      exact pos_of_mul_pos_right hr (Real.exp_pos _).le
    have hjVal : 0 < I.value j g := by
      unfold ratio at hRatio
      simpa only [zero_mul] using (lt_div_iff₀ (hVal g hg)).1 hRatio
    have hLinear : z i ≤ Real.log (ratio i j g) + z j + ε := by
      have hTerm : term z S = I.rivalThreshold (I.expWeights z) i g := by
        exact (term_eq z).trans ((max_eq_right br.le).trans hgEq)
      rw [hTerm, hj', hEntry z] at hUpper
      rwa [Real.log_mul (Real.exp_pos _).ne' hRatio.ne', Real.log_exp, add_comm (z j)] at hUpper
    let e : (some i : v) ⟶ some j := ⟨g, hVal g hg, hjVal, hLinear⟩
    have he := exact_edge e
    change x i ≤ Real.log (ratio i j g) + x j at he
    have hxExp : Real.exp (x i) ≤ rf x j := by
      rw [hEntry, mul_comm, ← Real.exp_log hRatio, ← Real.exp_add]
      exact Real.exp_le_exp.mpr he
    have hRx : rf x j ≤ I.rivalThreshold (I.expWeights x) i g :=
      Finset.le_sup' (rf x) (Finset.mem_univ j)
    rw [term_eq]
    exact hxExp.trans (hRx.trans ((Finset.le_sup' _ hg).trans (le_max_right _ _)))

theorem biased_greatest_gap (L : ℕ) (hL : I.LogInputBound L)
    (hrow : ∀ i, I.PositiveRow i) (w z : I.Weights)
    (hg : I.IsGreatestFeasible I.cap w) (hz : z ∈ I.cube (I.R L))
    (hfix : I.biasedMap L z = z) :
    ∀ i, I.logWeights w i ≤ z i ∧ z i ≤ I.logWeights w i + (I.n : ℝ) * I.repairSlack L := by
  let y := I.logWeights w
  let θ := I.bias L
  have hθ : 0 ≤ θ := by dsimp [θ, bias, precision]; positivity
  have hθ₁ : θ ≤ 1 := by
    dsimp [θ, bias, precision]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hc : 0 ≤ 1 - θ := sub_nonneg.mpr hθ₁
  have hFy (x : I.Weights) (i : I.Agent) : I.logThresholdMap x i ≤ I.logCap i :=
    min_le_left _ _
  have hExp : I.expWeights y = w := funext fun i => Real.exp_log (hg.1.1 i)
  have hyF : y ≤ I.logThresholdMap y := by
    apply (I.logMap_postfixed_iff y hrow).mpr
    rw [hExp]
    exact hg.1
  have hyH : y ≤ I.biasedMap L y := by
    intro i
    have hleft := mul_le_mul_of_nonneg_left (hyF i) hc
    have hright := mul_le_mul_of_nonneg_left ((hyF i).trans (hFy y i)) hθ
    change y i ≤ (1 - θ) * I.logThresholdMap y i + θ * I.logCap i
    linarith
  have hMono : Monotone (I.biasedMap L) := by
    intro a b hab i
    exact add_le_add (mul_le_mul_of_nonneg_left (I.logMap_monotone hab i) hc) le_rfl
  have hIter (k : ℕ) : y ≤ (I.biasedMap L)^[k] y := by
    induction k with
    | zero => exact le_rfl
    | succ k hk =>
      rw [Function.iterate_succ_apply']
      exact hyH.trans (hMono hk)
  have hcon := I.biased_map_contraction L hrow
  have hLimit := hcon.tendsto_iterate_fixedPoint y
  rw [← hcon.fixedPoint_unique hfix] at hLimit
  have hyz (i : I.Agent) : y i ≤ z i := ge_of_tendsto' (tendsto_pi_nhds.1 hLimit i)
    (fun k => hIter k i)
  have hFixed (i : I.Agent) : z i = (1 - θ) * I.logThresholdMap z i + θ * I.logCap i :=
    (congrFun hfix i).symm
  have hzcap : z ≤ I.logCap := by
    intro i
    have hle := mul_le_mul_of_nonneg_left (hFy z i) hc
    linarith [hFixed i]
  have happ (i : I.Agent) : z i ≤ I.logThresholdMap z i + I.repairSlack L := by
    have hLow := (abs_le.mp (I.logMap_mem_cube L hL hrow z i)).1
    have hCap : I.logCap i ≤ (I.R L : ℝ) := by
      change Real.log 4 ≤ (I.R L : ℝ)
      have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
      simp only [R, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
    have herr : I.logCap i - I.logThresholdMap z i ≤ 2 * (I.R L : ℝ) := by linarith
    have hdiff := mul_le_mul_of_nonneg_left herr hθ
    change z i ≤ I.logThresholdMap z i + 2 * (I.R L : ℝ) * θ
    linarith [hFixed i]
  obtain ⟨x, hx, hNear⟩ := I.repair_approx_postfixed L hL hrow z hzcap happ
  have hxw : I.expWeights x ≤ w := hg.2 ((I.logMap_postfixed_iff x hrow).mp hx)
  intro i
  refine ⟨hyz i, ?_⟩
  have hxy : x i ≤ y i := (Real.le_log_iff_exp_le (hg.1.1 i)).mpr (hxw i)
  linarith [(hNear i).1]

theorem approx_log_weights (L : ℕ) (hL : I.LogInputBound L)
    (hrow : ∀ i, I.PositiveRow i) (w z estimate : I.Weights)
    (hg : I.IsGreatestFeasible I.cap w) (hz : z ∈ I.cube (I.R L))
    (hfix : I.biasedMap L z = z) (hestimate : ‖estimate - z‖ ≤ precision (8 * I.P L)) :
    ‖estimate - I.logWeights w‖ < precision (7 * I.P L) := by
  let p := I.P L
  let E := precision (8 * p)
  have hE : 0 < E := by dsimp [E, precision]; positivity
  have hpPos : 0 < p := by dsimp [p, P]; positivity
  have hP : 1 ≤ p := Nat.one_le_of_lt hpPos
  have hPrec (a b : ℕ) : precision (a + b) = precision a * precision b := by
    simp only [precision, pow_add, mul_inv]
  have hCoefficientNat : 2 * I.n * I.R L ≤ p := by
    unfold p P R
    calc
      2 * I.n * (4 * (L + 1)) = (8 * I.n) * (L + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have hCoefficient : 2 * (I.n : ℝ) * (I.R L : ℝ) < 2 ^ (8 * p) := by
    have hNat : 2 * I.n * I.R L < (2 : ℕ) ^ p := hCoefficientNat.trans_lt Nat.lt_two_pow_self
    have hReal : 2 * (I.n : ℝ) * (I.R L : ℝ) < 2 ^ p := by exact_mod_cast hNat
    exact hReal.trans_le (pow_le_pow_right₀ (by norm_num) (by omega))
  have hSmall : 2 * (I.n : ℝ) * (I.R L : ℝ) * E < 1 := by
    dsimp only [E, precision]
    rwa [← div_eq_mul_inv, div_lt_one (by positivity)]
  have hSlack : (I.n : ℝ) * I.repairSlack L < E := by
    have hSplit : I.bias L = E * E := by
      change precision (16 * p) = _
      rw [show 16 * p = 8 * p + 8 * p by omega, hPrec]
    unfold repairSlack
    rw [hSplit]
    calc
      _ = (2 * (I.n : ℝ) * (I.R L : ℝ) * E) * E := by ring
      _ < 1 * E := mul_lt_mul_of_pos_right hSmall hE
      _ = E := one_mul _
  have hDist : ‖z - I.logWeights w‖ ≤ (I.n : ℝ) * I.repairSlack L := by
    have hNonneg : 0 ≤ (I.n : ℝ) * I.repairSlack L := by unfold repairSlack bias precision; positivity
    apply (pi_norm_le_iff_of_nonneg hNonneg).mpr
    intro i
    obtain ⟨hLo, hHi⟩ := I.biased_greatest_gap L hL hrow w z hg hz hfix i
    change |z i - I.logWeights w i| ≤ _
    rwa [abs_of_nonneg (sub_nonneg.mpr hLo), sub_le_iff_le_add, add_comm]
  have hTwice : E + E ≤ precision (7 * p) := by
    have hBase : (2 : ℝ) ≤ 2 ^ p := by
      simpa only [pow_one] using pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hP
    have hHalf : 2 * precision p ≤ 1 := by
      unfold precision
      rwa [← div_eq_mul_inv, div_le_one (by positivity)]
    have hSplit : E = precision p * precision (7 * p) := by
      change precision (8 * p) = _
      rw [show 8 * p = p + 7 * p by omega, hPrec]
    have hh : (2 * precision p) * precision (7 * p) ≤ 1 * precision (7 * p) :=
      mul_le_mul_of_nonneg_right hHalf (by unfold precision; positivity)
    rw [hSplit]
    linarith
  change ‖estimate - I.logWeights w‖ < precision (7 * p)
  calc
    _ = ‖(estimate - z) + (z - I.logWeights w)‖ := by congr 1; abel
    _ ≤ ‖estimate - z‖ + ‖z - I.logWeights w‖ := norm_add_le _ _
    _ < E + E := add_lt_add_of_le_of_lt hestimate (hDist.trans_lt hSlack)
    _ ≤ _ := hTwice

def AgentConnected (w : I.Weights) (root i : I.Agent) : Prop :=
  (I.highestBidderGraph w).Reachable (Sum.inl root) (Sum.inl i)

theorem exists_tight_agent_in_component (w : I.Weights) (_hcol : I.PositiveColumns)
    (hY : I.IsGreatestFeasible I.cap w) (root : I.Agent) :
    ∃ i, I.AgentConnected w root i ∧
      (w i = I.cap i ∨ I.bundlePrice w (I.forcedGoods w i) = 1) := by
  classical
  have hw : I.IsFeasible I.cap w := hY.1
  by_contra hnone
  let comp (i : I.Agent) : Prop := I.AgentConnected w root i
  let lift (t : ℝ) : I.Weights := fun i => if comp i then t * w i else w i
  have h1 : lift 1 = w := by
    funext i
    by_cases hi : comp i <;> simp [lift, hi]
  have hcap (i : I.Agent) (hi : comp i) : w i < I.cap i :=
    lt_of_le_of_ne (hw.2.1 i) (fun heq => hnone ⟨i, hi, Or.inl heq⟩)
  have hspend (i : I.Agent) (hi : comp i) : I.bundlePrice w (I.forcedGoods w i) < 1 :=
    lt_of_le_of_ne (hw.2.2 i) (fun heq => hnone ⟨i, hi, Or.inr heq⟩)
  have hlift (i : I.Agent) : Continuous (fun t => lift t i) := by
    by_cases hi : comp i
    · simp only [lift, hi, ite_true]
      fun_prop
    · simpa only [lift, hi, ite_false] using
        (continuous_const : Continuous (fun _ : ℝ => w i))
  let K : Set ℝ := {t | (∀ i : {i // comp i},
      lift t i < I.cap i ∧ t * I.bundlePrice w (I.forcedGoods w i) < 1) ∧
    ∀ g i j, I.bid w i g < I.bid w j g → I.bid (lift t) i g < I.bid (lift t) j g}
  have hK : IsOpen K := by
    unfold K
    rw [Set.ofPred_and]
    apply IsOpen.inter
    · rw [Set.ofPred_forall]
      refine isOpen_iInter_of_finite (fun i => ?_)
      rw [Set.ofPred_and]
      exact (isOpen_lt (hlift i) continuous_const).inter
        (isOpen_lt (continuous_id.mul continuous_const) continuous_const)
    · simp only [Set.ofPred_forall]
      refine isOpen_iInter_of_finite (fun g => isOpen_iInter_of_finite (fun i =>
        isOpen_iInter_of_finite (fun j => ?_)))
      by_cases hij : I.bid w i g < I.bid w j g
      · simp only [hij, Set.iInter_true]
        have hb (k : I.Agent) : Continuous (fun t => I.bid (lift t) k g) := by
          unfold bid
          exact (hlift k).mul (continuous_const : Continuous (fun _ : ℝ => I.value k g))
        exact isOpen_lt (hb i) (hb j)
      · simp [hij]
  have hOneK : (1 : ℝ) ∈ K := by
    change (∀ i : {i // comp i}, lift 1 i < I.cap i ∧
      1 * I.bundlePrice w (I.forcedGoods w i) < 1) ∧ _
    refine ⟨fun i => ?_, fun g i j hij => ?_⟩
    · simpa only [h1, one_mul] using And.intro (hcap i i.property) (hspend i i.property)
    · simpa only [h1] using hij
  obtain ⟨l, r, ⟨hl, hr⟩, hKr⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hK.mem_nhds hOneK)
  obtain ⟨t, ht, htr⟩ := exists_between hr
  have htK : t ∈ K := hKr ⟨hl.trans ht, htr⟩
  have hbound : (∀ i : {i // comp i}, lift t i < I.cap i ∧
      t * I.bundlePrice w (I.forcedGoods w i) < 1) := htK.1
  have hstrict (g : I.Good) (i j : I.Agent) (hij : I.bid w i g < I.bid w j g) :
      I.bid (lift t) i g < I.bid (lift t) j g := htK.2 g i j hij
  have hTies (g : I.Good) (i j : I.Agent) (hi : I.IsHighestBidder w i g)
      (hj : I.IsHighestBidder w j g) : I.bid (lift t) i g = I.bid (lift t) j g := by
    have hia : (I.highestBidderGraph w).Adj (Sum.inl i) (Sum.inr g) := by
      simpa [highestBidderGraph] using hi
    have hja : (I.highestBidderGraph w).Adj (Sum.inl j) (Sum.inr g) := by
      simpa [highestBidderGraph] using hj
    have hreach := hia.reachable.trans hja.symm.reachable
    have heqComp : comp i ↔ comp j :=
      ⟨fun hc => hc.trans hreach, fun hc => hc.trans hreach.symm⟩
    have hTie : w i * I.value i g = w j * I.value j g := (hj i).antisymm (hi j)
    by_cases hci : comp i
    · have hcj := heqComp.mp hci
      simp only [bid, lift, hci, hcj, ite_true, mul_assoc, hTie]
    · have hcj : ¬ comp j := fun hc => hci (heqComp.mpr hc)
      simpa only [bid, lift, hci, hcj, ite_false] using hTie
  have high_iff (i : I.Agent) (g : I.Good) :
      I.IsHighestBidder (lift t) i g ↔ I.IsHighestBidder w i g := by
    constructor
    · intro h
      by_contra hi
      obtain ⟨j, hj⟩ := not_forall.mp hi
      exact not_le_of_gt (hstrict g i j (lt_of_not_ge hj)) (h j)
    · intro hi j
      by_cases hj : I.IsHighestBidder w j g
      · exact (hTies g i j hi hj).ge
      · have hij : I.bid w j g < I.bid w i g := by
          refine lt_of_le_of_ne (hi j) (fun heq => hj ?_)
          exact fun k => (hi k).trans heq.ge
        exact (hstrict g j i hij).le
  have forced_iff (r : I.Weights) (i : I.Agent) (g : I.Good) :
      g ∈ I.forcedGoods r i ↔ I.IsHighestBidder r i g ∧
        ∀ j, j ≠ i → ¬ I.IsHighestBidder r j g := by
    simp only [forcedGoods, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hs
      refine ⟨fun j => ?_, fun j hj h => not_le_of_gt (hs j hj) (h i)⟩
      by_cases hj : j = i
      · simp [hj]
      · exact (hs j hj).le
    · rintro ⟨hi, huniq⟩ j hj
      refine lt_of_le_of_ne (hi j) (fun heq => huniq j hj ?_)
      exact fun k => (hi k).trans heq.ge
  have hGoods (i : I.Agent) : I.forcedGoods (lift t) i = I.forcedGoods w i := by
    ext g
    simp only [forced_iff, high_iff]
  have hPrice (i : I.Agent) (g : I.Good) (hg : g ∈ I.forcedGoods w i) :
      I.price (lift t) g = if comp i then t * I.price w g else I.price w g := by
    have hi := ((forced_iff w i g).1 hg).1
    have hnew := (high_iff i g).2 hi
    rw [← (I.highest_bidder_iff_bid_eq_price (lift t) i g).1 hnew,
      ← (I.highest_bidder_iff_bid_eq_price w i g).1 hi]
    by_cases hc : comp i <;> simp [bid, lift, hc, mul_assoc]
  have hf : I.IsFeasible I.cap (lift t) := by
    constructor
    · intro i
      by_cases hc : comp i
      · simpa only [lift, hc, ite_true] using mul_pos (zero_lt_one.trans ht) (hw.1 i)
      · simpa only [lift, hc, ite_false] using hw.1 i
    · constructor
      · intro i
        by_cases hc : comp i
        · exact (hbound ⟨i, hc⟩).1.le
        · simpa only [lift, hc, ite_false] using hw.2.1 i
      · intro i
        rw [hGoods]
        by_cases hc : comp i
        · have hEq : I.bundlePrice (lift t) (I.forcedGoods w i) =
              t * I.bundlePrice w (I.forcedGoods w i) := by
            simp only [bundlePrice, Finset.mul_sum]
            exact Finset.sum_congr rfl (fun g hg => by simpa [hc] using hPrice i g hg)
          rw [hEq]
          exact (hbound ⟨i, hc⟩).2.le
        · have hEq : I.bundlePrice (lift t) (I.forcedGoods w i) =
              I.bundlePrice w (I.forcedGoods w i) := by
            simp only [bundlePrice]
            exact Finset.sum_congr rfl (fun g hg => by simpa [hc] using hPrice i g hg)
          exact hEq.trans_le (hw.2.2 i)
  have hroot : comp root := SimpleGraph.Reachable.rfl
  have hIncrease : w root < lift t root := by
    simpa [lift, hroot] using mul_lt_mul_of_pos_right ht (hw.1 root)
  exact not_le_of_gt hIncrease (hY.2 hf root)

/-- Relative weights propagated along every bid tie, with unit weight at the root. -/
def IsRelativeWeight (w ρ : I.Weights) (root : I.Agent) : Prop :=
  ρ root = 1 ∧ ∀ (i j : I.Agent) (g : I.Good), I.AgentConnected w root i →
    I.IsHighestBidder w i g → I.IsHighestBidder w j g →
      ρ j = ρ i * I.value i g / I.value j g

theorem relative_weights_ratios (w ρ : I.Weights) (hcol : I.PositiveColumns)
    (hw : I.Positive w) (root : I.Agent) (hρ : I.IsRelativeWeight w ρ root) :
    ∀ i, I.AgentConnected w root i → w i = w root * ρ i := by
  let G := I.highestBidderGraph w
  let V := I.Agent ⊕ I.Good
  let goodRank (v : V) : Prop := match v with
    | Sum.inl k => w k = w root * ρ k
    | Sum.inr g => ∀ j, I.IsHighestBidder w j g → w j = w root * ρ j
  have hwalk {a b : V} (p : G.Walk a b) : a = Sum.inl root → goodRank b := by
    refine SimpleGraph.Walk.concatRec
      (motive := fun a b _ => a = Sum.inl root → goodRank b) ?_ ?_ p
    · intro a heq
      subst a
      simp [goodRank, hρ.1]
    · intro a b c p hadj ih heq
      have hpositive := ih heq
      have hreachable : G.Reachable (Sum.inl root) b := by rw [← heq]; exact ⟨p⟩
      cases b with
      | inl k =>
        cases c with
        | inl k' =>
          simp [G, highestBidderGraph] at hadj
        | inr g =>
          have hk : I.IsHighestBidder w k g := by simpa [G, highestBidderGraph] using hadj
          intro j hj
          obtain ⟨l, hl⟩ := hcol g
          have hlbid : 0 < I.bid w l g := mul_pos (hw l) hl
          have hjv : 0 < I.value j g :=
            pos_of_mul_pos_right (hlbid.trans_le (hj l)) (hw j).le
          have hratio : ρ j = ρ k * I.value k g / I.value j g :=
            hρ.2 k j g hreachable hk hj
          have hkval : w k = w root * ρ k := hpositive
          rw [hratio, ← mul_div_assoc, ← mul_assoc, ← hkval]
          exact (eq_div_iff hjv.ne').2 ((hk j).antisymm (hj k))
      | inr g =>
        cases c with
        | inl k =>
          have hk : I.IsHighestBidder w k g := by simpa [G, highestBidderGraph] using hadj
          exact hpositive k hk
        | inr g' =>
          simp [G, highestBidderGraph] at hadj
  intro i hi
  obtain ⟨p⟩ := hi
  exact hwalk p rfl

/-- The cap and the nonempty uniquely won bundles give the scale bounds. -/
def componentScaleBounds (w ρ : I.Weights) (root : I.Agent) : Set ℝ :=
  {s | ∃ i, I.AgentConnected w root i ∧
    (s = I.cap i / ρ i ∨ ((I.forcedGoods w i).Nonempty ∧
      s = (ρ i * I.utility i (I.forcedGoods w i))⁻¹))}

theorem component_scale_formula (w ρ : I.Weights) (hcol : I.PositiveColumns)
    (hY : I.IsGreatestFeasible I.cap w) (root : I.Agent)
    (hρ : I.IsRelativeWeight w ρ root) :
    IsLeast (I.componentScaleBounds w ρ root) (w root) := by
  have hw : I.IsFeasible I.cap w := hY.1
  have hratios := I.relative_weights_ratios w ρ hcol hw.1 root hρ
  have hpos (i : I.Agent) (hi : I.AgentConnected w root i) : 0 < ρ i := by
    have hMul : 0 < w root * ρ i := (hratios i hi) ▸ hw.1 i
    exact pos_of_mul_pos_right hMul (hw.1 root).le
  have hhighest (i : I.Agent) (g : I.Good) (hg : g ∈ I.forcedGoods w i) :
      I.IsHighestBidder w i g := by
    have hs : ∀ j, j ≠ i → I.bid w j g < I.bid w i g := by simpa [forcedGoods] using hg
    intro j
    by_cases hj : j = i
    · simp [hj]
    · exact (hs j hj).le
  have hspending (i : I.Agent) :
      I.bundlePrice w (I.forcedGoods w i) = w i * I.utility i (I.forcedGoods w i) := by
    simp only [bundlePrice, FairDivision.additiveValue, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun g hg =>
      ((I.highest_bidder_iff_bid_eq_price w i g).1 (hhighest i g hg)).symm)
  have hu (i : I.Agent) (hi : (I.forcedGoods w i).Nonempty) :
      0 < I.utility i (I.forcedGoods w i) := by
    apply Finset.sum_pos _ hi
    intro g hg
    obtain ⟨j, hj⟩ := hcol g
    have hbid : 0 < I.bid w i g := (mul_pos (hw.1 j) hj).trans_le (hhighest i g hg j)
    exact pos_of_mul_pos_right hbid (hw.1 i).le
  have hfactor (i : I.Agent) (hi : I.AgentConnected w root i) :
      w root * (ρ i * I.utility i (I.forcedGoods w i)) =
        I.bundlePrice w (I.forcedGoods w i) := by
    rw [← mul_assoc, ← hratios i hi, hspending]
  constructor
  · obtain ⟨i, hi, hiCap | hiSpend⟩ := I.exists_tight_agent_in_component w hcol hY root
    · refine ⟨i, hi, Or.inl ?_⟩
      apply (eq_div_iff (hpos i hi).ne').2
      rwa [← hratios i hi]
    · have hne : (I.forcedGoods w i).Nonempty := by
        by_contra hn
        have he := Finset.not_nonempty_iff_eq_empty.mp hn
        norm_num [he, bundlePrice] at hiSpend
      refine ⟨i, hi, Or.inr ⟨hne, ?_⟩⟩
      rw [← one_div]
      exact (eq_div_iff (mul_pos (hpos i hi) (hu i hne)).ne').2
        ((hfactor i hi).trans hiSpend)
  · rintro s ⟨i, hi, hcap | ⟨hne, hSpend⟩⟩
    · rw [hcap, le_div_iff₀ (hpos i hi), ← hratios i hi]
      exact hw.2.1 i
    · rw [hSpend, ← one_div, le_div_iff₀ (mul_pos (hpos i hi) (hu i hne)), hfactor i hi]
      exact hw.2.2 i

def WeightHeight (P' : ℕ) (w : I.Weights) : Prop :=
  ∀ i, ∃ q : ℚ, w i = (q : ℝ) ∧ 0 < q ∧ q.num.natAbs ≤ 2 ^ P' ∧ q.den ≤ 2 ^ P'

theorem weight_height_of_greatest (L : ℕ) (hL : I.LogInputBound L)
    (hcol : I.PositiveColumns) (w : I.Weights) (hY : I.IsGreatestFeasible I.cap w) :
    I.WeightHeight (I.P L) w := by
  classical
  have hw : I.IsFeasible I.cap w := hY.1
  let b₀ := L * (I.m + 2)
  have originalHeight (i : I.Agent) (g : I.Good) (hi : 0 < I.value i g) :
      RationalBounds.PositiveRatio (2 ^ L) (I.value i g) :=
    RationalBounds.of_rat _ (I.v i g) (by exact_mod_cast hi) (hL.2.2 i g).1 (hL.2.2 i g).2
  have positive_bidder (i : I.Agent) (g : I.Good) (hi : I.IsHighestBidder w i g) :
      0 < I.value i g := by
    obtain ⟨j, hj⟩ := hcol g
    exact pos_of_mul_pos_right ((mul_pos (hw.1 j) hj).trans_le (hi j)) (hw.1 i).le
  have anchor (i : I.Agent)
      (ht : w i = I.cap i ∨ I.bundlePrice w (I.forcedGoods w i) = 1) :
      RationalBounds.PositiveRatio (2 ^ b₀) (w i) := by
    rcases ht with hc | hs
    · have hbase : 2 ≤ b₀ := by
        have hl := Nat.le_mul_of_pos_right L (show 0 < I.m + 2 by omega)
        dsimp [b₀]
        have := hL.1
        omega
      have h4 : 4 ≤ (2 : ℕ) ^ b₀ := by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hbase
      exact ⟨4, 1, by decide, by decide, h4, (by omega), by rw [hc]; norm_num [cap]⟩
    · let S := I.forcedGoods w i
      let q : ℚ := ∑ g ∈ S, I.v i g
      have hqr : (q : ℝ) = I.utility i S := by simp [q, FairDivision.additiveValue]
      have hPay : I.bundlePrice w S = w i * I.utility i S := by
        simp only [bundlePrice, FairDivision.additiveValue, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g hg
        have hstrict : ∀ j, j ≠ i → I.bid w j g < I.bid w i g := by
          simpa [S, forcedGoods] using hg
        have hi : I.IsHighestBidder w i g := fun j => by
          by_cases hj : j = i
          · simp [hj]
          · exact (hstrict j hj).le
        exact ((I.highest_bidder_iff_bid_eq_price w i g).mp hi).symm
      have hProd : w i * (q : ℝ) = 1 := by rw [hqr, ← hPay]; exact hs
      have hqReal : 0 < (q : ℝ) := pos_of_mul_pos_right (by rw [hProd]; norm_num) (hw.1 i).le
      have hq : 0 < q := by exact_mod_cast hqReal
      have hWeight : w i = (q : ℝ)⁻¹ := by
        rw [← one_div]
        exact (eq_div_iff hqReal.ne').2 hProd
      have hCard : S.card ≤ I.m := by simpa using Finset.card_le_card (Finset.subset_univ S)
      have hM : I.m ≤ (2 : ℕ) ^ L := by
        have hm : I.m ≤ L := by have := hL.2.1; omega
        exact hm.trans (show L < (2 : ℕ) ^ L from Nat.lt_two_pow_self).le
      obtain ⟨hn, hd⟩ := RationalBounds.sum_num_den_bound S (I.v i) L
        (fun g _ => ⟨I.nonneg i g, (hL.2.2 i g).1, (hL.2.2 i g).2⟩)
      have hNum : q.num.natAbs ≤ 2 ^ b₀ := by
        calc
          _ ≤ S.card * 2 ^ (L * (S.card + 1)) := hn
          _ ≤ (2 : ℕ) ^ L * 2 ^ (L * (I.m + 1)) := Nat.mul_le_mul (hCard.trans hM)
            (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (Nat.succ_le_succ hCard)))
          _ = 2 ^ b₀ := by rw [← pow_add]; dsimp [b₀]; congr 1; ring
      have hDen : q.den ≤ 2 ^ b₀ := hd.trans
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (by omega)))
      rw [hWeight]
      exact RationalBounds.inv_ratio (RationalBounds.of_rat _ q hq hNum hDen)
  let V := I.Agent ⊕ I.Good
  let G : SimpleGraph V := I.highestBidderGraph w
  let point (v : V) : ℝ := match v with
    | Sum.inl i => w i
    | Sum.inr g => I.price w g
  have along {a b : V} (p : G.Walk a b) : RationalBounds.PositiveRatio (2 ^ b₀) (point a) →
      RationalBounds.PositiveRatio (2 ^ (b₀ + L * p.length)) (point b) := by
    refine SimpleGraph.Walk.concatRec
      (motive := fun a b p => RationalBounds.PositiveRatio (2 ^ b₀) (point a) →
        RationalBounds.PositiveRatio (2 ^ (b₀ + L * p.length)) (point b)) ?_ ?_ p
    · intro a h
      simpa using h
    · intro a b c p hAdj ih hStart
      have hPrior := ih hStart
      rw [SimpleGraph.Walk.length_concat, Nat.mul_succ, ← Nat.add_assoc, pow_add]
      cases b with
      | inl i =>
        cases c with
        | inl j => simp [G, highestBidderGraph] at hAdj
        | inr g =>
          have hi : I.IsHighestBidder w i g := by simpa [G, highestBidderGraph] using hAdj
          have heq := (I.highest_bidder_iff_bid_eq_price w i g).mp hi
          change RationalBounds.PositiveRatio _ (I.price w g)
          rw [← heq]
          exact RationalBounds.mul_ratio hPrior (originalHeight i g (positive_bidder i g hi))
      | inr g =>
        cases c with
        | inl i =>
          have hi : I.IsHighestBidder w i g := by simpa [G, highestBidderGraph] using hAdj
          have hp := positive_bidder i g hi
          have heq : w i = I.price w g / I.value i g :=
            (eq_div_iff hp.ne').2 ((I.highest_bidder_iff_bid_eq_price w i g).mp hi)
          change RationalBounds.PositiveRatio _ (w i)
          rw [heq, div_eq_mul_inv]
          exact RationalBounds.mul_ratio hPrior (RationalBounds.inv_ratio (originalHeight i g hp))
        | inr g' => simp [G, highestBidderGraph] at hAdj
  intro i
  obtain ⟨j, hj, hTight⟩ := I.exists_tight_agent_in_component w hcol hY i
  have hReach : G.Reachable (Sum.inl j) (Sum.inl i) := hj.symm
  obtain ⟨p, hp⟩ := hReach.exists_isPath
  have hLen : p.length ≤ I.n + I.m := by
    have hCard := hp.support_nodup.length_le_card
    rw [SimpleGraph.Walk.length_support, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hCard
    omega
  have hExp : b₀ + L * p.length ≤ I.P L := by
    unfold P
    dsimp [b₀]
    rw [← Nat.mul_add]
    calc
      _ ≤ (L + 1) * (16 * (I.n + I.m + 1)) := Nat.mul_le_mul (Nat.le_succ L) (by omega)
      _ = _ := Nat.mul_comm _ _
  exact RationalBounds.to_rat _ _ <|
    RationalBounds.mono_ratio (along p (anchor j hTight)) (Nat.pow_le_pow_right (by decide) hExp)

noncomputable def trueLogBid (w : I.Weights) (i : I.Agent) (g : I.Good) : ℝ :=
  Real.log (w i) + Real.log (I.value i g)

theorem definite_log_bid_gap (L : ℕ) (hL : I.LogInputBound L)
    (w : I.Weights) (hwt : I.WeightHeight (I.P L) w)
    (i j : I.Agent) (g : I.Good) (hi : 0 < I.value i g) (hj : 0 < I.value j g)
    (hlt : I.bid w i g < I.bid w j g) :
    precision (3 * I.P L) ≤ I.trueLogBid w j g - I.trueLogBid w i g := by
  obtain ⟨qi, hwi, hqi, hqinum, hqiden⟩ := hwt i
  obtain ⟨qj, hwj, hqj, hqjnum, hqjden⟩ := hwt j
  obtain ⟨hvinum, hviden⟩ := hL.2.2 i g
  obtain ⟨hvjnum, hvjden⟩ := hL.2.2 j g
  have hvi : 0 < I.v i g := by exact_mod_cast hi
  have hvj : 0 < I.v j g := by exact_mod_cast hj
  have hwi' : 0 < w i := by rw [hwi]; exact_mod_cast hqi
  have hwj' : 0 < w j := by rw [hwj]; exact_mod_cast hqj
  have hbi : 0 < I.bid w i g := mul_pos hwi' hi
  have hbj : 0 < I.bid w j g := mul_pos hwj' hj
  let a := qj.num.natAbs * (I.v j g).num.natAbs * qi.den * (I.v i g).den
  let b := qi.num.natAbs * (I.v i g).num.natAbs * qj.den * (I.v j g).den
  have num_pos (q : ℚ) (hq : 0 < q) : 0 < q.num.natAbs :=
    Int.natAbs_pos.mpr (Rat.num_pos.mpr hq).ne'
  have ha : 0 < a := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (num_pos qj hqj)
    (num_pos (I.v j g) hvj)) (Rat.den_pos _)) (Rat.den_pos _)
  have hb : 0 < b := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (num_pos qi hqi)
    (num_pos (I.v i g) hvi)) (Rat.den_pos _)) (Rat.den_pos _)
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have rep (q : ℚ) (hq : 0 < q) : (q : ℝ) = (q.num.natAbs : ℝ) / (q.den : ℝ) := by
    rw [Rat.cast_def]
    have hn : (q.num : ℝ) = (q.num.natAbs : ℝ) := by
      have hnInt : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (Rat.num_pos.mpr hq).le
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) hnInt.symm
    rw [hn]
  have hratio : I.bid w j g / I.bid w i g = (a : ℝ) / (b : ℝ) := by
    change w j * ((I.v j g : ℚ) : ℝ) / (w i * ((I.v i g : ℚ) : ℝ)) = _
    simp only [hwi, hwj, rep qi hqi, rep qj hqj, rep (I.v i g) hvi,
      rep (I.v j g) hvj, a, b, Nat.cast_mul]
    have hposqi : (0 : ℝ) < qi.num.natAbs := by exact_mod_cast num_pos qi hqi
    have hposvi : (0 : ℝ) < (I.v i g).num.natAbs := by exact_mod_cast num_pos (I.v i g) hvi
    field_simp [hposqi.ne', hposvi.ne', Rat.den_nz]
  have haUpper : a ≤ 2 ^ (I.P L + L + I.P L + L) := by
    simp only [pow_add]
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hqjnum hvjnum) hqiden) hviden
  have hLP : 2 * L ≤ I.P L := by
    unfold P
    exact Nat.mul_le_mul (by omega) (Nat.le_succ L)
  have haUpper' : (a : ℝ) ≤ (2 : ℝ) ^ (3 * I.P L) := by
    have hpow : (2 : ℕ) ^ (I.P L + L + I.P L + L) ≤ 2 ^ (3 * I.P L) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact_mod_cast haUpper.trans hpow
  have hprecision : precision (3 * I.P L) ≤ (a : ℝ)⁻¹ := inv_anti₀ ha' haUpper'
  have hr : (1 : ℝ) < (a : ℝ) / (b : ℝ) := by
    rw [← hratio, lt_div_iff₀ hbi, one_mul]
    exact hlt
  have hba : b < a := by
    rw [lt_div_iff₀ hb', one_mul] at hr
    exact_mod_cast hr
  have hbOne : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hba
  have hInvGap : (b : ℝ) / (a : ℝ) + (a : ℝ)⁻¹ ≤ 1 := by
    rw [← one_div, ← add_div, div_le_one ha']
    exact hbOne
  have hloga := Real.log_le_sub_one_of_pos (div_pos hb' ha')
  rw [Real.log_div hb'.ne' ha'.ne'] at hloga
  have htrue : I.trueLogBid w j g - I.trueLogBid w i g = Real.log ((a : ℝ) / (b : ℝ)) := by
    rw [← hratio, Real.log_div hbj.ne' hbi.ne']
    simp [trueLogBid, bid, Real.log_mul hwi'.ne' hi.ne', Real.log_mul hwj'.ne' hj.ne']
  rw [htrue, Real.log_div ha'.ne' hb'.ne']
  linarith

def LogBidsAccurate (w : I.Weights) (approx : I.Agent → I.Good → ℝ) (ε : ℝ) : Prop :=
  ∀ i g, 0 < I.value i g → |approx i g - I.trueLogBid w i g| ≤ ε

/-- Discard zero valuations and keep the agents within `δ` of the highest
computed log bid. -/
def WithinComputedMax (approx : I.Agent → I.Good → ℝ) (δ : ℝ) (i : I.Agent)
    (g : I.Good) : Prop :=
  0 < I.value i g ∧ ∀ j, 0 < I.value j g → approx j g - approx i g ≤ δ

/-- Independent classification theorem using only accuracy and separation. -/
theorem classify_bidders_from_gap (w : I.Weights) (hw : I.Positive w)
    (hcol : I.PositiveColumns) (approx : I.Agent → I.Good → ℝ) (ε δ : ℝ)
    (hacc : I.LogBidsAccurate w approx ε) (hmargin : 2 * ε ≤ δ)
    (hgap : ∀ i j g, 0 < I.value i g → 0 < I.value j g → I.bid w i g < I.bid w j g →
      δ + 2 * ε < I.trueLogBid w j g - I.trueLogBid w i g) :
    ∀ i g, I.WithinComputedMax approx δ i g ↔ I.IsHighestBidder w i g := by
  intro i g
  constructor
  · rintro ⟨hi, hnear⟩ j
    by_contra hj_le
    have hlt : I.bid w i g < I.bid w j g := lt_of_not_ge hj_le
    have hbpos : 0 < I.bid w i g := mul_pos (hw i) hi
    have hj : 0 < I.value j g := pos_of_mul_pos_right (hbpos.trans hlt) (hw j).le
    have hsep := hgap i j g hi hj hlt
    have hi_err := (abs_le.mp (hacc i g hi)).2
    have hj_err := (abs_le.mp (hacc j g hj)).1
    have hj_near := hnear j hj
    linarith
  · intro hmax
    obtain ⟨k, hk⟩ := hcol g
    have hkpos : 0 < I.bid w k g := mul_pos (hw k) hk
    have hipos : 0 < I.bid w i g := hkpos.trans_le (hmax k)
    have hi : 0 < I.value i g := pos_of_mul_pos_right hipos (hw i).le
    refine ⟨hi, fun j hj => ?_⟩
    have hjpos : 0 < I.bid w j g := mul_pos (hw j) hj
    have hlogs := (Real.log_le_log_iff hjpos hipos).2 (hmax j)
    have htrue : I.trueLogBid w j g ≤ I.trueLogBid w i g := by
      simpa [trueLogBid, bid, Real.log_mul (hw j).ne' hj.ne', Real.log_mul (hw i).ne' hi.ne']
        using hlogs
    have hi_err := (abs_le.mp (hacc i g hi)).1
    have hj_err := (abs_le.mp (hacc j g hj)).2
    linarith

theorem classify_bidders_at_precision (L : ℕ) (hL : I.LogInputBound L)
    (w : I.Weights) (hcol : I.PositiveColumns) (hwt : I.WeightHeight (I.P L) w)
    (approx : I.Agent → I.Good → ℝ)
    (hacc : I.LogBidsAccurate w approx (2 * precision (7 * I.P L))) :
    ∀ i g, I.WithinComputedMax approx (precision (4 * I.P L)) i g ↔
      I.IsHighestBidder w i g := by
  have hw : I.Positive w := by
    intro i
    obtain ⟨q, hq, hpos, _, _⟩ := hwt i
    rw [hq]
    exact_mod_cast hpos
  let p := I.P L
  have hp : 1 ≤ p := by
    change 1 ≤ 16 * (I.n + I.m + 1) * (L + 1)
    exact Nat.succ_le_of_lt (by positivity)
  have positive (k : ℕ) : 0 < precision k := by
    unfold precision
    positivity
  have mono : Antitone precision := by
    intro a b hab
    exact inv_anti₀ (by positivity : 0 < (2 : ℝ) ^ a)
      (pow_le_pow_right₀ (by norm_num) hab)
  have add_prec (a b : ℕ) : precision (a + b) = precision a * precision b := by
    simp only [precision, pow_add, mul_inv]
  have h7 : precision (7 * p) = precision (3 * p) * precision (4 * p) := by
    rw [show 7 * p = 3 * p + 4 * p by omega, add_prec]
  have h4 : precision (4 * p) = precision p * precision (3 * p) := by
    rw [show 4 * p = p + 3 * p by omega, add_prec]
  have h3small : precision (3 * p) ≤ 1 / 8 := by
    have h := mono (show 3 ≤ 3 * p by omega)
    norm_num [precision] at h ⊢
    exact h
  have h1small : precision p ≤ 1 / 2 := by
    have h := mono hp
    norm_num [precision] at h ⊢
    exact h
  have h7Bound : 4 * precision (7 * p) ≤ (1 / 2) * precision (4 * p) := by
    rw [h7]
    have h := mul_le_mul_of_nonneg_right h3small (positive (4 * p)).le
    linarith
  have h4Bound : precision (4 * p) ≤ (1 / 2) * precision (3 * p) := by
    rw [h4]
    exact mul_le_mul_of_nonneg_right h1small (positive (3 * p)).le
  have hmargin : 2 * (2 * precision (7 * p)) ≤ precision (4 * p) := by
    linarith [positive (4 * p)]
  have hgapMargin : precision (4 * p) + 2 * (2 * precision (7 * p)) < precision (3 * p) := by
    linarith [positive (3 * p)]
  refine I.classify_bidders_from_gap w hw hcol approx _ _ hacc hmargin (fun i j g hi hj hlt => ?_)
  exact hgapMargin.trans_le (I.definite_log_bid_gap L hL w hwt i j g hi hj hlt)

end EF1FPO.Instance
