import EF1FPO.EvaluationMath

/-! Convert the checked fixed-point error to exact greatest-weight bid membership. -/

set_option autoImplicit false

namespace EF1FPO.GreatestGraphStage

open OAI.Optimization.LinearProgramming.OracleSpec

structure Guess where
  prepared : PreparedInput
  precision : ℕ
  grid : GridNumerator prepared.inst.n
  cube : unitCube (dyadicPoint precision grid)
  approximate : ∃ v : Vector prepared.inst.n,
    unitCube v ∧ prepared.inst.normalizedBiasedMap (valuationBits prepared.inst) v = v ∧
      ∀ i, |(logRadius prepared.inst : ℝ) * (dyadicPoint precision grid i - v i)| ≤
        precisionError (8 * weightBits prepared.inst)

def Guess.encode (g : Guess) : Word :=
  frame (encodeInstance g.prepared.inst) ++ encodeUnary g.precision ++ encodeGrid g.grid

def Guess.asQuery (g : Guess) : EvaluationInput :=
  ⟨g.prepared, g.precision, 0, g.grid, g.cube⟩

noncomputable def Guess.logBid (g : Guess) (i : g.prepared.inst.Agent)
    (j : g.prepared.inst.Good) : ℚ :=
  g.asQuery.scaledPoint i + guardedLog (g.prepared.inst.v i j) (7 * weightBits g.prepared.inst)

noncomputable def Guess.mask (g : Guess) : BidderMask g.prepared.inst := by
  classical
  let I := g.prepared.inst
  exact fun i j => decide (
    0 < I.v i j ∧ ∀ k, 0 < I.v k j →
      g.logBid k j - g.logBid i j ≤ ((2 : ℚ) ^ (4 * weightBits I))⁻¹)

theorem guess_exists (d : PreparedInput) (word : Word) (h : approximateOutput d word) :
    ∃ g : Guess, g.prepared = d ∧ g.encode = frame (encodeInstance d.inst) ++ word := by
  obtain ⟨s, q, v, hCube, hv, hFixed, hNear, hw⟩ := h
  exact ⟨⟨d, s, q, hCube, v, hv, hFixed, hNear⟩, rfl,
    by rw [hw]; simp only [Guess.encode, List.append_assoc]⟩

theorem Guess.mask_correct (g : Guess) : IsGreatestBidderMask g.prepared.inst g.mask := by
  let I := g.prepared.inst
  let L := valuationBits I
  let P := weightBits I
  let R : ℝ := logRadius I
  let estimate (i : I.Agent) : ℝ := g.asQuery.scaledPoint i
  obtain ⟨v, hCube, hFixed, hNear⟩ := g.approximate
  let z (i : I.Agent) : ℝ := R * v i
  have hR : 0 < R := by dsimp [R, logRadius]; positivity
  have zCube : z ∈ I.cube (I.R L) := by
    intro i
    change |R * v i| ≤ R
    rw [abs_mul, abs_of_nonneg hR.le]
    exact mul_le_of_le_one_right hR.le (abs_le.mpr (hCube i))
  have zFixed : I.biasedMap L z = z := by
    funext i
    have h := congrFun hFixed i
    change I.biasedMap L z i / R = v i at h
    exact ((div_eq_iff hR.ne').mp h).trans (mul_comm _ _)
  have hRow (i : I.Agent) : I.PositiveRow i := by
    obtain ⟨j, hj⟩ := g.prepared.preparation.prepared_positive_agents g.prepared.valid i
    exact ⟨j, by exact_mod_cast hj⟩
  have hCol : I.PositiveColumns := by
    intro j
    obtain ⟨i, hi⟩ := g.prepared.preparation.prepared_positive_goods g.prepared.valid j
    exact ⟨i, by exact_mod_cast hi⟩
  have hVal : I.LogInputBound L := valuationBits_logInputBound I
  obtain ⟨w, hGreatest, _, _⟩ := I.greatest_weights I.cap (fun _ => by norm_num [Instance.cap])
    (g.prepared.preparation.prepared_cap_covers g.prepared.valid)
  have estimateSpec (i : I.Agent) : estimate i = R * dyadicPoint g.precision g.grid i := by
    simp [estimate, I, R, Guess.asQuery, EvaluationInput.scaledPoint, dyadicPoint,
      precisionError, div_eq_mul_inv]
  have precNonneg (k : ℕ) : 0 ≤ Instance.precision k := by unfold Instance.precision; positivity
  have estimateNear : ‖(estimate : I.Weights) - z‖ ≤ Instance.precision (8 * I.P L) := by
    apply (pi_norm_le_iff_of_nonneg (precNonneg _)).mpr
    intro i
    change ‖estimate i - z i‖ ≤ precisionError (8 * P)
    rw [Real.norm_eq_abs, estimateSpec, show z i = R * v i from rfl, ← mul_sub]
    exact hNear i
  have normNear := I.approx_log_weights L hVal hRow w z estimate hGreatest zCube zFixed estimateNear
  let b (i : I.Agent) (j : I.Good) : ℝ := g.logBid i j
  have hBid : I.LogBidsAccurate w b (2 * Instance.precision (7 * I.P L)) := by
    intro i j hv
    let ε := Instance.precision (7 * I.P L)
    have point := (pi_norm_le_iff_of_nonneg (precNonneg _)).mp normNear.le i
    change ‖estimate i - I.logWeights w i‖ ≤ ε at point
    rw [Real.norm_eq_abs] at point
    have positive : 0 < I.v i j := by exact_mod_cast hv
    have logErr := guardedLog_error (I.v i j) (7 * P) positive
    simp only [b, Guess.logBid, Rat.cast_add, Instance.trueLogBid]
    change |estimate i + (guardedLog (I.v i j) (7 * P) : ℝ) -
      (I.logWeights w i + Real.log (I.value i j))| ≤ 2 * ε
    have algebra : estimate i + (guardedLog (I.v i j) (7 * P) : ℝ) -
        (I.logWeights w i + Real.log (I.value i j)) =
        (estimate i - I.logWeights w i) + ((guardedLog (I.v i j) (7 * P) : ℝ) - Real.log (I.value i j)) := by ring
    rw [algebra]
    exact (abs_add_le _ _).trans (by linarith only [add_le_add point (show
      |(guardedLog (I.v i j) (7 * P) : ℝ) - Real.log (I.value i j)| ≤ ε from logErr)])
  have ties := I.classify_bidders_at_precision L hVal w hCol
    (I.weight_height_of_greatest L hVal hCol w hGreatest) b hBid
  refine ⟨w, hGreatest, fun i j => ?_⟩
  rw [← ties i j]
  simp only [Guess.mask, decide_eq_true_eq, Instance.WithinComputedMax]
  have tolerance : (((2 : ℚ) ^ (4 * P))⁻¹ : ℝ) = Instance.precision (4 * I.P L) := by
    simp [Instance.precision, P, weightBits, Instance.P, L, I]
  have bid i j : (g.logBid i j : ℝ) = b i j := rfl
  constructor
  · rintro ⟨hOwn, every⟩
    refine ⟨by exact_mod_cast hOwn, fun k hk => ?_⟩
    have pos : 0 < I.v k j := by exact_mod_cast hk
    have h := every k pos
    rw [← tolerance, ← bid k j, ← bid i j, ← Rat.cast_sub]
    exact_mod_cast h
  · rintro ⟨hOwn, every⟩
    refine ⟨by exact_mod_cast hOwn, fun k hk => ?_⟩
    have pos : 0 < I.value k j := by exact_mod_cast hk
    have h := every k pos
    rw [← tolerance, ← bid k j, ← bid i j, ← Rat.cast_sub] at h
    exact_mod_cast h

end EF1FPO.GreatestGraphStage
