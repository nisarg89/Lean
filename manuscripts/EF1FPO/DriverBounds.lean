import EF1FPO.DriverSession
import EF1FPO.DriverWires
import EF1FPO.GridBounds

/-! Word lengths and query counts in the actual monotone-contraction controller. -/

set_option autoImplicit false

namespace EF1FPO.BisectionDriver

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.Optimization.LinearProgramming.PriceGame

def Input.size (input : Input) : ℕ := input.n + input.b + input.k + 1

noncomputable def campaignHeight : Polynomial ℕ :=
  (Polynomial.C 16 * Polynomial.X) ^ 1510

theorem campaign_height_bound (p : Progress) :
    (Control.campaignSolver Campaign.rounds p.publicInput).height ≤ campaignHeight.eval p.input.size := by
  let s := p.s
  have hRange : p.publicInput.range = 2 ^ (s + 1) := by
    simp [Progress.publicInput, s, pow_succ, Nat.mul_comm]
  have hPower : 2 ≤ (2 : ℕ) ^ (s + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      (show 1 ≤ s + 1 by omega)
  have hRangePositive : p.publicInput.range + 1 ≠ 0 := by omega
  have hBits : (p.publicInput.range + 1).log2 < s + 2 := by
    apply (Nat.log2_lt hRangePositive).mpr
    rw [hRange, show s + 2 = (s + 1) + 1 by omega, pow_succ]
    omega
  have hPublic : p.publicInput.goods + (p.publicInput.range + 1).log2 + 1 ≤ 8 * p.input.size := by
    change p.input.n + (p.publicInput.range + 1).log2 + 1 ≤ 8 * p.input.size
    dsimp [s, Progress.s] at hBits
    unfold Input.size
    omega
  rw [campaignHeight, Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  calc
    (Control.campaignSolver Campaign.rounds p.publicInput).height ≤
        2 ^ 1510 * (p.publicInput.goods + (p.publicInput.range + 1).log2 + 1) ^ 1510 :=
      Control.campaignSolver_queryBound p.publicInput
    _ ≤ 2 ^ 1510 * (8 * p.input.size) ^ 1510 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hPublic _)
    _ = (16 * p.input.size) ^ 1510 := by rw [← mul_pow]; congr 1 <;> omega

theorem progress_word_bound (p : Progress) (v : ℕ → ℝ) (valid : p.Valid v) :
    (encodeProgress p).length ≤ 200 * p.input.size ^ 2 := by
  rcases valid with ⟨hRound, _, loCube, loContains, hiContains, hiCube, _, hCount, hDone⟩
  let k := p.input.k
  let x := p.input.size
  have hInteger (z : ℤ) (below : -1 ≤ bisectionCoordinate k z) (above : bisectionCoordinate k z ≤ 1) :
      (intCode z).length ≤ 2 * k + 9 := by
    have hSize : z.natAbs.size ≤ bisectionGrid k + 1 :=
      (Nat.size_le_size (dyadic_numerator_bound (bisectionGrid k) z below above)).trans_eq Nat.size_pow
    have hBits : z.natAbs.bits.length = z.natAbs.size := Nat.size_eq_bits_len z.natAbs
    simp only [intCode, intData, prodCode, pairBits_length, Procedure.boolCode,
      List.length_cons, List.length_nil]
    unfold bisectionGrid at hSize
    omega
  have hLoWord := hInteger p.bounds.1 loCube (loContains.trans (hiContains.trans hiCube))
  have hHiWord := hInteger p.bounds.2 (loCube.trans (loContains.trans hiContains)) hiCube
  have hCompleted (z : ℤ) (hz : z ∈ p.completed) : (intCode z).length ≤ 2 * k + 9 := by
    have hReverse : z ∈ p.completed.reverse := by simpa using hz
    obtain ⟨j, hj, hzVal⟩ := List.mem_iff_getElem.mp hReverse
    have hEarlier : j < p.index.val := by simpa only [List.length_reverse, hCount] using hj
    obtain ⟨w, hw, hGood⟩ := hDone j hEarlier
    rw [List.getElem?_eq_getElem hj, hzVal] at hw
    have hEq : z = w := Option.some.inj hw
    exact hEq.symm ▸ hInteger w hGood.1 hGood.2.1
  have hList : (listCode intCode p.completed).length ≤ p.completed.length * (2 * (2 * k + 9) + 2) + 1 := by
    simpa only [List.map_id] using listCode_length_map_bound intCode id p.completed (2 * k + 9) hCompleted
  have hIndex := p.index.isLt
  have hOne : 1 ≤ x := by dsimp [x, Input.size]; omega
  have hLinear : x ≤ x ^ 2 := by
    rw [pow_two]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left x hOne
  have hLength : p.completed.length ≤ x := by dsimp [x, Input.size]; omega
  have hCoeff : 2 * (2 * k + 9) + 2 ≤ 24 * x := by dsimp [k, x, Input.size]; omega
  have hListBound : (listCode intCode p.completed).length ≤ 24 * x ^ 2 + 1 := by
    calc
      (listCode intCode p.completed).length ≤ p.completed.length * (2 * (2 * k + 9) + 2) + 1 := hList
      _ ≤ x * (24 * x) + 1 := Nat.add_le_add_right (Nat.mul_le_mul hLength hCoeff) 1
      _ = 24 * x ^ 2 + 1 := by ring
  have hN : p.input.n ≤ x := by dsimp [x, Input.size]; omega
  have hB : p.input.b ≤ x := by dsimp [x, Input.size]; omega
  have hK : k ≤ x := by dsimp [k, x, Input.size]; omega
  change (encodeProgress p).length ≤ 200 * x ^ 2
  simp only [encodeProgress, boundsCode, prodCode, pairBits_length, unaryCode, List.length_replicate]
  change p.round < k + 2 at hRound
  omega

theorem driver_word_bound :
    ∃ L : Polynomial ℕ,
      (∀ input : Input,
        (WordDialogue.inputCode encodeInput encodeCarry encodeReply (.inl input)).length ≤ L.eval input.size) ∧
      (∀ (input : Input) (a : GridNumerator input.n), unitCube (dyadicPoint (bisectionGrid input.k) a) →
        (encodeUnary (bisectionGrid input.k) ++ encodeGrid a).length ≤ L.eval input.size) ∧
      ∀ (p : Progress) (v : ℕ → ℝ), p.Valid v → ∀ (replies : List Bool) (q : Query p.input.n),
        p.observe replies = .inr q → ∀ answer : GridNumerator p.input.n,
        unitCube (dyadicPoint p.s answer) →
        (suspend p replies q).1.length ≤ L.eval p.input.size ∧
        (encodeGrid answer).length ≤ L.eval p.input.size ∧
        (WordDialogue.inputCode encodeInput encodeCarry encodeReply
          (.inr ⟨(suspend p replies q).2, answer⟩)).length ≤ L.eval p.input.size := by
  let quadratic : Polynomial ℕ := Polynomial.X ^ 2
  let jobWidth := Polynomial.C 400 * quadratic + campaignHeight + 1
  let replayWidth := jobWidth + replayP.bound.comp jobWidth
  let requestWidth := replayWidth + requestActionP.bound.comp replayWidth
  let width := Polynomial.C 100 * quadratic + requestWidth
  have hJobAt (x : ℕ) : jobWidth.eval x = 400 * x ^ 2 + campaignHeight.eval x + 1 := by
    simp only [jobWidth, quadratic, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  have hReplayAt (x : ℕ) :
      replayWidth.eval x = jobWidth.eval x + replayP.bound.eval (jobWidth.eval x) := by
    simp only [replayWidth, Polynomial.eval_add, Polynomial.eval_comp]
  have hRequestAt (x : ℕ) :
      requestWidth.eval x = replayWidth.eval x + requestActionP.bound.eval (replayWidth.eval x) := by
    simp only [requestWidth, Polynomial.eval_add, Polynomial.eval_comp]
  have hWidthAt (x : ℕ) : width.eval x = 100 * x ^ 2 + requestWidth.eval x := by
    simp only [width, quadratic, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  have hOne (x : Input) : 1 ≤ x.size := by unfold Input.size; omega
  have hDimension (x : Input) : x.n ≤ x.size := by unfold Input.size; omega
  have hSquare (x : Input) : x.size ≤ x.size ^ 2 := by
    rw [pow_two]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left x.size (hOne x)
  have hGrid (x : Input) (s : ℕ) (a : GridNumerator x.n) (h : unitCube (dyadicPoint s a))
      (fit : 2 * s + 7 ≤ 21 * x.size) : (encodeGrid a).length ≤ 21 * x.size ^ 2 := by
    calc
      (encodeGrid a).length ≤ x.n * (2 * s + 7) := encodeGrid_length_of_cube s a h
      _ ≤ x.size * (21 * x.size) := Nat.mul_le_mul (hDimension x) fit
      _ = 21 * x.size ^ 2 := by ring
  refine ⟨width, ?_, ?_, ?_⟩
  · intro x
    have hText :
        (WordDialogue.inputCode encodeInput encodeCarry encodeReply (.inl x)).length = x.size + 3 := by
      simp only [WordDialogue.inputCode, encodeInput, contractionInput, encodeUnary,
        List.length_cons, List.length_append, List.length_replicate, List.length_nil, Input.size]
      omega
    rw [hText, hWidthAt]
    have h := hSquare x
    have one := hOne x
    omega
  · intro x a hCube
    have hFit : 2 * bisectionGrid x.k + 7 ≤ 21 * x.size := by
      unfold bisectionGrid Input.size
      omega
    have hNumerators := hGrid x (bisectionGrid x.k) a hCube hFit
    have hHead : (encodeUnary (bisectionGrid x.k)).length ≤ 8 * x.size := by
      simp only [encodeUnary, bisectionGrid, List.length_append, List.length_replicate, List.length_cons,
        List.length_nil, Input.size]
      omega
    rw [List.length_append, hWidthAt]
    have h := hSquare x
    omega
  · intro p v valid replies q visible answer hCube
    let x := p.input.size
    let job : ReplayJob := (p, replies)
    let pending : Pending := ⟨job, q⟩
    let strategy := Control.campaignSolver Campaign.rounds p.publicInput
    have hObs : Control.observe strategy replies.reverse = .inr q := visible
    obtain ⟨_, _, hReplies⟩ := Control.pending_of_observe strategy replies.reverse hObs
    rw [List.length_reverse] at hReplies
    have repliesBound : replies.length ≤ campaignHeight.eval x :=
      (show replies.length ≤ strategy.height by omega).trans (campaign_height_bound p)
    have progressBound := progress_word_bound p v valid
    have inputBound : (encodeJob job).length ≤ jobWidth.eval x := by
      rw [hJobAt]
      simp only [encodeJob, job, prodCode, pairBits_length, id_eq]
      change (encodeProgress p).length ≤ 200 * x ^ 2 at progressBound
      omega
    have hReplay : replay job = .inr pending :=
      congrArg (replayResultAt job) visible
    have hPending := (replayP.output_length_le job).trans
      (Nat.add_le_add inputBound (Procedure.eval_nat_mono _ inputBound))
    rw [hReplay, ← hReplayAt] at hPending
    simp only [encodeReplayResult, sumCode, List.length_cons] at hPending
    have hPendingBound : (encodePending pending).length ≤ replayWidth.eval x := by omega
    have hRequest := (requestActionP.output_length_le pending).trans
      (Nat.add_le_add hPendingBound (Procedure.eval_nat_mono _ hPendingBound))
    rw [← hRequestAt] at hRequest
    have hParts : 2 * (suspend p replies q).1.length + (encodeCarry (suspend p replies q).2).length + 2 ≤
        requestWidth.eval x := by
      simp only [WordDialogue.actionCode, pending, job, List.length_cons, List.length_append,
        frame_length] at hRequest
      omega
    have hAnswerFit : 2 * p.s + 7 ≤ 21 * p.input.size := by unfold Progress.s Input.size; omega
    have hAnswer := hGrid p.input p.s answer hCube hAnswerFit
    change (encodeGrid answer).length ≤ 21 * x ^ 2 at hAnswer
    have hLinear := hSquare p.input
    have one : 1 ≤ x := hOne p.input
    refine ⟨?_, ?_, ?_⟩
    · rw [hWidthAt]
      change (suspend p replies q).1.length ≤ 100 * x ^ 2 + requestWidth.eval x
      omega
    · rw [hWidthAt]
      change (encodeGrid answer).length ≤ 100 * x ^ 2 + requestWidth.eval x
      omega
    · rw [hWidthAt]
      simp only [WordDialogue.inputCode, encodeReply, List.length_cons, List.length_append, frame_length]
      change 2 * (encodeGrid answer).length + 1 + (encodeCarry (suspend p replies q).2).length + 1 ≤
        100 * x ^ 2 + requestWidth.eval x
      change x ≤ x ^ 2 at hLinear
      omega

end EF1FPO.BisectionDriver
