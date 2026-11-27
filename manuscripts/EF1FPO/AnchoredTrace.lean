import EF1FPO.PricePackets
import OAI.Optimization.LinearProgramming.PriceGame.ControlSign

/-! Relate a single campaign's binary comparisons to the actual dyadic oracle history. -/

set_option autoImplicit false

namespace EF1FPO

open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.Optimization.LinearProgramming.PriceGame

def campaignRequest {n : ℕ} (b k : ℕ) (anchor : Fin n) (threshold : ℚ) (query : Query n) :
    AnchoredPriceRequest :=
  ⟨n, b + k + 6, anchor, query.index, threshold, query.prices⟩

def campaignAnswer (q : AnchoredPriceRequest) (answer : GridNumerator q.n) : AnchoredPriceAnswer :=
  ⟨q.n, q.precision, q.designated, q.raw q.designated, answer⟩

noncomputable def AnchoredHidden {n : ℕ} (v : Vector n) (hv : unitCube v) (s : ℕ) (a : Fin n) (up : Bool) :
    Hidden n (2 * 2 ^ s) a :=
  ⟨up, Finset.univ, Finset.mem_univ a, fun i =>
    ⟨anchoredCost v up s i, Nat.lt_succ_of_le (anchored_cost_le v hv up s i)⟩⟩

inductive AnchoredTrace {n : ℕ} (f : Vector n → Vector n) (reply : WordOracle)
    (b k : ℕ) (a : Fin n) (t : ℚ) :
    Computation n Bool → Transcript → Bool → Transcript → ℕ → Prop where
  | done (bit : Bool) (history : Transcript) :
      AnchoredTrace f reply b k a t (.pure bit) history bit history 0
  | query {query : Query n} {next : Bool → Computation n Bool}
      {history final : Transcript} {bit : Bool} {rounds : ℕ}
      (answer : GridNumerator n)
      (cube : unitCube (dyadicPoint (b + k + 6) answer))
      (accurate : dist (dyadicPoint (b + k + 6) answer)
        (f (dyadicPoint (b + k + 6) (campaignRequest b k a t query).grid)) ≤ precisionError (b + k + 6))
      (wire : reply history (dyadicQuery (b + k + 6) (b + k + 6) (campaignRequest b k a t query).grid)
        = encodeGrid answer)
      (rest : AnchoredTrace f reply b k a t
        (next (campaignAnswer (campaignRequest b k a t query) answer).compare)
        ((dyadicQuery (b + k + 6) (b + k + 6) (campaignRequest b k a t query).grid, encodeGrid answer) :: history)
        bit final rounds) :
      AnchoredTrace f reply b k a t (.ask query next) history bit final (rounds + 1)

theorem anchoredTrace_exists {n b k : ℕ} {f : Vector n → Vector n} {reply : WordOracle}
    (hOracle : ApproximationOracle f reply) (a : Fin n) (t : ℚ)
    (strategy : Computation n Bool) (history : Transcript) :
    ∃ bit final rounds, rounds ≤ strategy.height ∧
      AnchoredTrace f reply b k a t strategy history bit final rounds := by
  induction strategy generalizing history with
  | pure value =>
    exact ⟨value, history, 0, Nat.zero_le _, .done value history⟩
  | ask query next ih =>
    let q := campaignRequest b k a t query
    let s := b + k + 6
    let packet := dyadicQuery s s q.grid
    obtain ⟨answer, hCube, hAccuracy, hWord⟩ := hOracle history s s q.grid q.grid_correct.1
    let comparison := (campaignAnswer q answer).compare
    obtain ⟨bit, final, rounds, hRounds, hTail⟩ :=
      ih comparison ((packet, encodeGrid answer) :: history)
    have hHeight : (next comparison).height ≤ max (next false).height (next true).height := by
      cases comparison with
      | false => exact le_max_left _ _
      | true => exact le_max_right _ _
    exact ⟨bit, final, rounds + 1, Nat.add_le_add_right (hRounds.trans hHeight) 1,
      .query answer hCube hAccuracy hWord hTail⟩

theorem anchoredTrace_reaches {n b k : ℕ} {f : Vector n → Vector n} {reply : WordOracle}
    {v : Vector n} (hf : MonotoneContraction f b) (hv : unitCube v) (hFixed : f v = v)
    {a : Fin n} {t : ℚ} {up : Bool}
    (gap : precisionError (k + 2) ≤ signFactor up * (v a - (t : ℝ)))
    {strategy : Computation n Bool} {history final : Transcript} {bit : Bool} {rounds : ℕ}
    (run : AnchoredTrace f reply b k a t strategy history bit final rounds) :
    Computation.Reaches (AnchoredHidden v hv (b + k + 6) a up) strategy bit := by
  induction run with
  | done value _ => exact .pure value
  | @query query next history final value rounds answer hCube hApprox hWord rest ih =>
    let q := campaignRequest b k a t query
    refine Computation.Reaches.ask (reply := (campaignAnswer q answer).compare) ?_ ih
    intro forced
    have minimum (j : Fin n) :
        adjustedCost up (anchoredCost v up (b + k + 6)) query.prices query.index ≤
          adjustedCost up (anchoredCost v up (b + k + 6)) query.prices j := by
      let hidden := AnchoredHidden v hv (b + k + 6) a up
      have active : j ∈ hidden.active := Finset.mem_univ _
      have hCost (i : Fin n) : (hidden.cost i : ℕ) = anchoredCost v up (b + k + 6) i := rfl
      have hSign (p : ℚ) : hidden.signedPrice p = (if up then p else -p) := rfl
      have bound := forced.2 j active
      change ((hidden.cost query.index : ℕ) : ℚ) + hidden.signedPrice (query.prices query.index) ≤
        ((hidden.cost j : ℕ) : ℚ) + hidden.signedPrice (query.prices j) at bound
      rw [hCost, hCost, hSign, hSign] at bound
      exact bound
    exact anchored_dyadic_reply f v hf hv hFixed a query.index t up query.prices gap minimum
      q.grid answer q.grid_correct.1 q.grid_correct.2 hApprox

end EF1FPO
