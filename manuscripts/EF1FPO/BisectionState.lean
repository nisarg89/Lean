import EF1FPO.Contraction
import OAI.Optimization.LinearProgramming.PriceGame.ControlSign

/-! Integer controller state and the first campaign query. -/

set_option autoImplicit false

namespace EF1FPO

open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.Optimization.LinearProgramming.PriceGame

def bisectionGrid (k : ℕ) : ℕ := 2 * k + 5

def bisectionMargin (k : ℕ) : ℤ := 2 ^ (k + 3)

def bisectionInitial (k : ℕ) : ℤ × ℤ :=
  (-((2 : ℤ) ^ bisectionGrid k), (2 : ℤ) ^ bisectionGrid k)

def bisectionMidpoint (bounds : ℤ × ℤ) : ℤ := (bounds.1 + bounds.2) / 2

def bisectionNext (k : ℕ) (bounds : ℤ × ℤ) (positive : Bool) : ℤ × ℤ :=
  let mid := bisectionMidpoint bounds
  if positive then (max bounds.1 (mid - bisectionMargin k), bounds.2)
  else (bounds.1, min bounds.2 (mid + bisectionMargin k))

def bisectionAligned (k j : ℕ) (bounds : ℤ × ℤ) : Prop :=
  (2 : ℤ) ^ (k + 3 - j) ∣ bounds.1 ∧ (2 : ℤ) ^ (k + 3 - j) ∣ bounds.2

noncomputable def bisectionCoordinate (k : ℕ) (x : ℤ) : ℝ :=
  (x : ℝ) * precisionError (bisectionGrid k)

theorem bisection_initial_aligned (k : ℕ) : bisectionAligned k 0 (bisectionInitial k) := by
  have h : (2 : ℤ) ^ (k + 3) ∣ (2 : ℤ) ^ bisectionGrid k :=
    pow_dvd_pow 2 (by unfold bisectionGrid; omega)
  exact ⟨dvd_neg.mpr h, h⟩

theorem bisection_margin_coordinate (k : ℕ) :
    bisectionCoordinate k (bisectionMargin k) = precisionError (k + 2) := by
  unfold bisectionCoordinate bisectionMargin precisionError bisectionGrid
  push_cast
  rw [show 2 * k + 5 = (k + 3) + (k + 2) by omega, pow_add (2 : ℝ) (k + 3) (k + 2)]
  field_simp

theorem bisection_midpoint_coordinate {k j : ℕ} (bounds : ℤ × ℤ) (hRound : j < k + 2)
    (hAligned : bisectionAligned k j bounds) :
    bisectionCoordinate k (bisectionMidpoint bounds) =
      (bisectionCoordinate k bounds.1 + bisectionCoordinate k bounds.2) / 2 := by
  have hDiv : (2 : ℤ) ∣ (2 : ℤ) ^ (k + 3 - j) := by
    simpa only [pow_one] using (pow_dvd_pow (2 : ℤ) (show 1 ≤ k + 3 - j by omega))
  have hSum : (2 : ℤ) ∣ bounds.1 + bounds.2 :=
    (hDiv.trans hAligned.1).add (hDiv.trans hAligned.2)
  have hTwice := Int.ediv_mul_cancel hSum
  have hCast := congrArg (fun z : ℤ => (z : ℝ)) hTwice
  push_cast at hCast
  have hMid : (bisectionMidpoint bounds : ℝ) = ((bounds.1 : ℝ) + (bounds.2 : ℝ)) / 2 :=
    (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).mpr hCast
  unfold bisectionCoordinate
  rw [hMid]
  ring

theorem bisection_next_aligned {k j : ℕ} (bounds : ℤ × ℤ) (positive : Bool) (hRound : j < k + 2)
    (hAligned : bisectionAligned k j bounds) :
    bisectionAligned k (j + 1) (bisectionNext k bounds positive) := by
  let e := k + 3 - (j + 1)
  let d : ℤ := 2 ^ e
  have hExponent : k + 3 - j = e + 1 := by dsimp [e]; omega
  have hPower : (2 : ℤ) ^ (k + 3 - j) = d * 2 := by rw [hExponent, pow_succ]
  have hSmall : d ∣ (2 : ℤ) ^ (k + 3 - j) := pow_dvd_pow 2 (by dsimp [e]; omega)
  have hLower := hSmall.trans hAligned.1
  have hUpper := hSmall.trans hAligned.2
  have hMargin : d ∣ bisectionMargin k := pow_dvd_pow 2 (Nat.sub_le _ _)
  have hMid : d ∣ bisectionMidpoint bounds := by
    obtain ⟨a, ha⟩ := hAligned.1
    obtain ⟨b, hb⟩ := hAligned.2
    refine ⟨a + b, ?_⟩
    rw [bisectionMidpoint, ha, hb, hPower]
    rw [show d * 2 * a + d * 2 * b = (d * (a + b)) * 2 by ring]
    exact Int.mul_ediv_cancel _ (by decide)
  cases positive
  · change d ∣ bounds.1 ∧ d ∣ min bounds.2 (bisectionMidpoint bounds + bisectionMargin k)
    refine ⟨hLower, ?_⟩
    rw [min_def]
    split
    · exact hUpper
    · exact hMid.add hMargin
  · change d ∣ max bounds.1 (bisectionMidpoint bounds - bisectionMargin k) ∧ d ∣ bounds.2
    refine ⟨?_, hUpper⟩
    rw [max_def]
    split
    · exact hMid.sub hMargin
    · exact hLower

theorem campaign_initial_queries (i : Control.PublicInput) (hRange : 0 < i.range) :
    ∃ (packet : Word) (carry : Control.Tape),
      Control.dispatch (Control.campaignSolver Campaign.rounds) (.inl i) = .inr (packet, carry) := by
  have firstQuery (solver : Control.PublicSolver) (input : Control.PublicInput)
      (correct : ∀ (h : Hidden input.goods input.range input.anchor) (bit : Bool),
        Computation.Reaches h (solver input) bit → bit = h.positive) :
      ∃ (packet : Word) (carry : Control.Tape),
        Control.dispatch solver (.inl input) = .inr (packet, carry) := by
    apply Classical.byContradiction
    intro failure
    cases hs : solver input with
    | pure bit =>
      let witness (b : Bool) : Hidden input.goods input.range input.anchor :=
        ⟨b, {input.anchor}, Finset.mem_singleton_self _, fun _ => ⟨0, Nat.succ_pos _⟩⟩
      have h (b : Bool) : bit = b := by
        apply correct (witness b) bit
        rw [hs]
        exact Computation.Reaches.pure bit
      exact Bool.noConfusion ((h false).symm.trans (h true))
    | ask q _ =>
      apply failure
      refine ⟨priceQuery q.index q.prices, Control.startTape (.inl input), ?_⟩
      apply (Control.dispatch_query_iff solver (.inl input) _ _).mpr
      refine ⟨rfl, q, ?_, rfl⟩
      change Control.observe (solver input) [] = .inr q
      rw [hs]
      rfl
  exact firstQuery (Control.campaignSolver Campaign.rounds) i (Control.campaignSolver_recover i hRange)

end EF1FPO
