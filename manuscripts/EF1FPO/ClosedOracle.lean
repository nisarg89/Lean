import EF1FPO.BisectionDriver
import EF1FPO.Controller
import EF1FPO.EvaluationMath

/-! The checked rational evaluator supplies the contraction controller's exact reply words. -/

set_option autoImplicit false

namespace EF1FPO.ClosedApproximation

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.Optimization.LinearProgramming.PriceGame (Query)
open EF1FPO.BisectionDriver

noncomputable section

abbrev Event := WordDialogue.Event Input Carry Reply

def source (d : PreparedInput) : Input :=
  ⟨d.inst.n, 16 * weightBits d.inst, 9 * weightBits d.inst, d.inst.hn⟩

def eventInput : Event → Input
  | .inl input => input
  | .inr ⟨carry, _⟩ => carry.progress.input

def inputCode (d : PreparedInput) : Word := encodeInstance d.inst

def requestInput (d : PreparedInput) (packet : Word) :=
  { request : EvaluationInput // request.prepared = d ∧ request.encode = frame (inputCode d) ++ packet }

def answer (d : PreparedInput) : WordOracle := by
  classical
  exact fun _ packet => if h : Nonempty (requestInput d packet) then
    encodeGrid (Classical.choice h).val.rounded else []

theorem encodeGrid_injective (n : ℕ) : Function.Injective (encodeGrid (n := n)) := by
  intro a b h
  let av := List.ofFn (fun i => (a i : ℚ))
  let bv := List.ofFn (fun i => (b i : ℚ))
  have raw : av.flatMap encodeRat ++ [] = bv.flatMap encodeRat ++ [] := by
    simpa only [av, bv, encodeGrid, List.append_nil] using h
  have listEq := ((encodeRats_prefix av bv (by simp [av, bv]) [] []).mp raw).1
  have funcEq := List.ofFn_injective listEq
  funext i
  exact_mod_cast congrFun funcEq i

theorem matching_request_output (a b : EvaluationInput) (hPrepared : a.prepared = b.prepared)
    (hWord : a.encode = b.encode) : encodeGrid a.rounded = encodeGrid b.rounded := by
  have unarySplit (p p' : ℕ) (xs ys : Word) (h : encodeUnary p ++ xs = encodeUnary p' ++ ys) :
      p = p' ∧ xs = ys := by
    induction p generalizing p' with
    | zero =>
      cases p' with
      | zero => simpa [encodeUnary] using h
      | succ p' => simp [encodeUnary, List.replicate_succ] at h
    | succ p ih =>
      cases p' with
      | zero => simp [encodeUnary, List.replicate_succ] at h
      | succ p' =>
        have hTail : encodeUnary p ++ xs = encodeUnary p' ++ ys := by
          simpa [encodeUnary, List.replicate_succ] using h
        obtain ⟨rfl, rfl⟩ := ih p' hTail
        exact ⟨rfl, rfl⟩
  rcases a with ⟨d, p, s, q, hq⟩
  rcases b with ⟨d', p', s', q', hq'⟩
  change d = d' at hPrepared
  subst d'
  have hPacket : dyadicQuery p s q = dyadicQuery p' s' q' := List.append_cancel_left hWord
  have separate : encodeUnary p ++ (encodeUnary s ++ encodeGrid q) =
      encodeUnary p' ++ (encodeUnary s' ++ encodeGrid q') := by
    simpa only [dyadicQuery, List.append_assoc] using hPacket
  obtain ⟨rfl, hp⟩ := unarySplit _ _ _ _ separate
  obtain ⟨rfl, hGrid⟩ := unarySplit _ _ _ _ hp
  have equal := encodeGrid_injective d.inst.n hGrid
  subst q'
  rfl

theorem answer_agrees (d : PreparedInput) (packet : Word) (r : requestInput d packet)
    (history : Transcript) : answer d history packet = encodeGrid r.val.rounded := by
  classical
  have available : Nonempty (requestInput d packet) := ⟨r⟩
  unfold answer
  rw [dite_eq_left available]
  let chosen : requestInput d packet := Classical.choice available
  exact matching_request_output chosen.val r.val
    (chosen.property.1.trans r.property.1.symm) (chosen.property.2.trans r.property.2.symm)

theorem dispatch_query_shape (event : Event) (packet : Word) (carry : Carry)
    (h : BisectionDriver.dispatch event = .inr (packet, carry)) :
    carry.progress.input = eventInput event ∧
      ∃ (p s : ℕ) (q : GridNumerator carry.progress.input.n),
        unitCube (dyadicPoint p q) ∧ packet = dyadicQuery p s q := by
  let valid (input : Input) (packet : Word) (carry : Carry) :=
    carry.progress.input = input ∧ ∃ (p s : ℕ) (q : GridNumerator carry.progress.input.n),
      unitCube (dyadicPoint p q) ∧ packet = dyadicQuery p s q
  have suspended (p : Progress) (replies : List Bool) (q : Query p.input.n) :
      valid p.input (suspend p replies q).1 (suspend p replies q).2 := by
    let r := campaignRequest p.input.b p.input.k p.index p.threshold q
    exact ⟨rfl, p.s, p.s, r.grid, r.grid_correct.1, rfl⟩
  have fromLaunch (p : Progress) (h : launch p = .inr (packet, carry)) : valid p.input packet carry := by
    obtain ⟨q, hq⟩ := launch_pending p
    have eq := Sum.inr.inj (hq.symm.trans h)
    exact (congrArg (fun z : Word × Carry => valid p.input z.1 z.2) eq).mp (suspended p [] q)
  have preserved (p p' : Progress) (b : Bool) (h : p.advance b = .inr p') : p'.input = p.input := by
    unfold Progress.advance at h
    split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · cases h
  have fromObservation (p : Progress) (xs : List Bool) (obs : (Bool × List Bool) ⊕ Query p.input.n)
      (h : actionAt p xs obs = .inr (packet, carry)) : valid p.input packet carry := by
    rcases obs with ⟨b, bs⟩ | q
    · cases hAdvance : p.advance b with
      | inl result => simp only [actionAt, afterSign, hAdvance, renderAdvance, reduceCtorEq] at h
      | inr p' =>
        have earlier := fromLaunch p' (by simpa only [actionAt, afterSign, hAdvance, renderAdvance] using h)
        exact ⟨earlier.1.trans (preserved p p' b hAdvance), earlier.2⟩
    · have eq := Sum.inr.inj h
      exact (congrArg (fun z : Word × Carry => valid p.input z.1 z.2) eq).mp (suspended p xs q)
  rcases event with input | ⟨previous, response⟩
  · exact fromLaunch (initial input) h
  · let xs := previous.compare response :: previous.replies
    exact fromObservation previous.progress xs (previous.progress.observe xs) h

theorem answer_legal (d : PreparedInput) :
    ApproximationOracle (d.inst.normalizedBiasedMap (valuationBits d.inst)) (answer d) := by
  intro history p s a hCube
  let r : EvaluationInput := ⟨d, p, s, a, hCube⟩
  let request : requestInput d (dyadicQuery p s a) := ⟨r, rfl, rfl⟩
  obtain ⟨q, hReplyCube, hReplyDistance, hWire⟩ := r.rounded_correct
  exact ⟨q, hReplyCube, hReplyDistance,
    (answer_agrees d (dyadicQuery p s a) request history).trans hWire⟩

theorem bounded_sessions :
    ∃ ticks capacity : Polynomial ℕ, ∀ d : PreparedInput,
      ∃ result history rounds,
        rounds ≤ ticks.eval (inputCode d).length ∧ approximateOutput d result ∧
        WordDialogue.Session encodeInput encodeCarry encodeReply BisectionDriver.dispatch (answer d)
          (capacity.eval (inputCode d).length) (.inl (source d)) [] result history rounds := by
  obtain ⟨width, count, bounded⟩ := BisectionDriver.bounded_session
  let majorant : Polynomial ℕ := Polynomial.C 500 * (Polynomial.X + Polynomial.C 5) ^ 2
  refine ⟨count.comp majorant, width.comp majorant, fun d => ?_⟩
  let I := d.inst
  let L := valuationBits I
  let P := weightBits I
  let ℓ := (inputCode d).length
  let f := I.normalizedBiasedMap L
  let a := source d
  let size := a.n + a.b + a.k + 1
  have shape : I.n + I.m ≤ ℓ := dimensions_le_binarySize I
  have hL : L ≤ ℓ + 4 := by
    change max 4 (max (I.n + I.m) ℓ) ≤ ℓ + 4
    omega
  have hP : P ≤ 16 * (ℓ + 5) ^ 2 := by
    have first : I.n + I.m + 1 ≤ ℓ + 5 := by omega
    have second : L + 1 ≤ ℓ + 5 := by omega
    calc
      P = 16 * ((I.n + I.m + 1) * (L + 1)) := by dsimp [P, weightBits, L]; ring
      _ ≤ 16 * ((ℓ + 5) * (ℓ + 5)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul first second)
      _ = _ := by rw [pow_two]
  have hSize : size ≤ majorant.eval ℓ := by
    simp only [majorant, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_X]
    change I.n + 16 * P + 9 * P + 1 ≤ 500 * (ℓ + 5) ^ 2
    have hSquare : ℓ + 1 ≤ (ℓ + 5) ^ 2 := by nlinarith
    calc
      _ ≤ 401 * (ℓ + 5) ^ 2 := by omega
      _ ≤ 500 * (ℓ + 5) ^ 2 := Nat.mul_le_mul_right _ (by norm_num)
  let hC : MonotoneContraction f a.b := prepared_normalized_map_contract d
  obtain ⟨v, ⟨hCube, hFixed⟩, _⟩ := monotone_contraction_fixed_point f hC
  obtain ⟨result, history, rounds, hRounds, run, _, s, q, hQ, hNear, hOut⟩ :=
    bounded a f v (answer d) hC hCube hFixed (answer_legal d)
  have enlarge {lo hi : ℕ} (h : lo ≤ hi) {event : Event} {past trail : Transcript} {result : Word} {n : ℕ}
      (run : WordDialogue.Session encodeInput encodeCarry encodeReply BisectionDriver.dispatch
        (answer d) lo event past result trail n) :
      WordDialogue.Session encodeInput encodeCarry encodeReply BisectionDriver.dispatch
        (answer d) hi event past result trail n := by
    induction run with
    | done finished input output => exact .done finished (input.trans h) (output.trans h)
    | query pending input packet reply ans encoded next ih =>
      exact .query pending (input.trans h) (packet.trans h) (reply.trans h) ans encoded ih
  refine ⟨result, history, rounds, hRounds.trans ?_, ?_, enlarge ?_ run⟩
  · rw [Polynomial.eval_comp]
    exact Procedure.eval_nat_mono count hSize
  · refine ⟨s, q, v, hQ, hCube, hFixed, fun i => ?_, hOut⟩
    let R : ℝ := logRadius I
    have hR : 0 ≤ R := by dsimp [R]; positivity
    have radiusNat : logRadius I ≤ P := by
      dsimp [logRadius, P, weightBits]
      exact Nat.mul_le_mul_right _ (by omega)
    have radiusReal : R ≤ (2 : ℝ) ^ P := by
      change (logRadius I : ℝ) ≤ _
      exact_mod_cast radiusNat.trans (show P < (2 : ℕ) ^ P from Nat.lt_two_pow_self).le
    have exponent : precisionError (9 * P) = precisionError P * precisionError (8 * P) := by
      rw [show 9 * P = P + 8 * P by omega]
      simp only [precisionError, pow_add, mul_inv]
    have cancel : (2 : ℝ) ^ P * precisionError P = 1 := mul_inv_cancel₀ (by positivity)
    have error := (dist_le_pi_dist (dyadicPoint s q) v i).trans hNear
    change dist (dyadicPoint s q i) (v i) ≤ precisionError (9 * P) at error
    change |R * (dyadicPoint s q i - v i)| ≤ precisionError (8 * P)
    rw [abs_mul, abs_of_nonneg hR]
    calc
      _ ≤ R * precisionError (9 * P) :=
        mul_le_mul_of_nonneg_left (by simpa only [Real.dist_eq] using error) hR
      _ ≤ (2 : ℝ) ^ P * precisionError (9 * P) :=
        mul_le_mul_of_nonneg_right radiusReal (by unfold precisionError; positivity)
      _ = precisionError (8 * P) := by rw [exponent, ← mul_assoc, cancel, one_mul]
  · rw [Polynomial.eval_comp]
    exact Procedure.eval_nat_mono width hSize

end

end EF1FPO.ClosedApproximation
