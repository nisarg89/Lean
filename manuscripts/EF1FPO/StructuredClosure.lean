import EF1FPO.WordDialogue
import OAI.Optimization.LinearProgramming.OracleSpec.GuardedIteration

/-! Compose the actual finite procedures and close a checked word dialogue. -/

set_option autoImplicit false

namespace EF1FPO

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.Optimization.LinearProgramming.OracleSpec

noncomputable def composeRetainingInput {X M Y Z : Type}
    {input : X → Word} {middle : M → Word} {nextInput : Y → Word} {output : Z → Word}
    {firstValue : X → M} {lastValue : Y → Z}
    (first : Procedure input middle firstValue) (second : Procedure nextInput output lastValue)
    (bridge : X → Y)
    (wire : ∀ x, nextInput (bridge x) = frame (input x) ++ middle (firstValue x)) :
    Procedure input output (lastValue ∘ bridge) := by
  let retained := (Procedure.identity input).pair first
  let matched : Procedure input nextInput bridge := retained.result (by
    intro x
    rw [wire x]
    simp [prodCode, pairBits, quoteBits_eq_frame])
  exact second.comp matched

namespace WordDialogue

noncomputable def closeWithProcedures {X S I C : Type} {Reply : C → Type}
    {input : X → Word} {stateCode : S → Word}
    {initState : X → S} {step : S → S} {output : S → Word}
    (source : X → I) (view : S → X × (Event I C Reply ⊕ Word))
    (ei : I → Word) (ec : C → Word) (er : ∀ carry, Reply carry → Word)
    (dispatch : Dispatch I C Reply) (reply : X → WordOracle)
    (startP : Procedure input stateCode initState)
    (stepP : Procedure stateCode stateCode step)
    (outputP : Procedure stateCode id output)
    (ticks capacity width : Polynomial ℕ)
    (hStart : ∀ x, view (initState x) = (x, .inl (.inl (source x))))
    (hDone : ∀ x s event result, view s = (x, .inl event) → dispatch event = .inl result →
      view (step s) = (x, .inr result))
    (hQuery : ∀ x s event history packet carry answer,
      view s = (x, .inl event) → dispatch event = .inr (packet, carry) →
      er carry answer = reply x history packet →
      view (step s) = (x, .inl (.inr ⟨carry, answer⟩)))
    (hStop : ∀ x s result, view s = (x, .inr result) → step s = s ∧ output s = result)
    (hWidth : ∀ x s, (view s).1 = x →
      (match (view s).2 with
       | .inl event => (inputCode ei ec er event).length
       | .inr result => result.length) ≤ capacity.eval (input x).length →
      (stateCode s).length ≤ width.eval (input x).length)
    (post : X → Word → Prop)
    (hSessions : ∀ x, ∃ result history rounds,
      rounds ≤ ticks.eval (input x).length ∧ post x result ∧
      Session ei ec er dispatch (reply x) (capacity.eval (input x).length)
        (.inl (source x)) [] result history rounds) :
    let computed := fun x => output ((step^[ticks.eval (input x).length]) (initState x))
    { machine : Procedure input id computed // ∀ x, post x (computed x) } := by
  let wordLength (s : S) : ℕ :=
    match (view s).2 with
    | .inl event => (inputCode ei ec er event).length
    | .inr result => result.length
  have follows {x : X} {event : Event I C Reply} {past final : Transcript}
      {result : Word} {n : ℕ}
      (session : Session ei ec er dispatch (reply x) (capacity.eval (input x).length)
        event past result final n) (s : S) (seen : view s = (x, .inl event)) :
      view ((step^[n]) s) = (x, .inr result) ∧
      ∀ j ≤ n, (view ((step^[j]) s)).1 = x ∧
        wordLength ((step^[j]) s) ≤ capacity.eval (input x).length := by
    induction session generalizing s with
    | @done current past result stopped hInput hOutput =>
      have finished := hDone x s current result seen stopped
      refine ⟨by simpa only [Function.iterate_one] using finished, ?_⟩
      intro j hj
      obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
      · constructor
        · rw [Function.iterate_zero]; exact congrArg Prod.fst seen
        · simpa only [Function.iterate_zero, id_eq, wordLength, seen] using hInput
      · constructor
        · rw [Function.iterate_one]; exact congrArg Prod.fst finished
        · simpa only [Function.iterate_one, wordLength, finished] using hOutput
    | @query current past packet carry result final n pending hInput hPacket hReply answer hEncode rest ih =>
      have received := hQuery x s current past packet carry answer seen pending hEncode
      obtain ⟨finished, sizes⟩ := ih (step s) received
      refine ⟨by simpa only [Function.iterate_succ_apply] using finished, ?_⟩
      intro j hj
      cases j with
      | zero =>
        constructor
        · rw [Function.iterate_zero]; exact congrArg Prod.fst seen
        · simpa only [Function.iterate_zero, id_eq, wordLength, seen] using hInput
      | succ j =>
        have smaller := sizes j (Nat.le_of_succ_le_succ hj)
        simpa only [Function.iterate_succ_apply] using smaller
  have evaluated (x : X) :
      ∃ result n, n ≤ ticks.eval (input x).length ∧ post x result ∧
        view ((step^[n]) (initState x)) = (x, .inr result) ∧
        ∀ j ≤ n, (view ((step^[j]) (initState x))).1 = x ∧
          wordLength ((step^[j]) (initState x)) ≤ capacity.eval (input x).length := by
    obtain ⟨result, history, n, hClock, hPost, run⟩ := hSessions x
    obtain ⟨hResult, hSteps⟩ := follows run (initState x) (hStart x)
    exact ⟨result, n, hClock, hPost, hResult, hSteps⟩
  have chanceWidth (x : X) (j : ℕ) (_ : j < ticks.eval (input x).length) :
      (stateCode ((step^[j]) (initState x))).length ≤ width.eval (input x).length := by
    obtain ⟨result, n, _, _, hResult, hSteps⟩ := evaluated x
    have fits : (view ((step^[j]) (initState x))).1 = x ∧
        wordLength ((step^[j]) (initState x)) ≤ capacity.eval (input x).length := by
      by_cases hs : j ≤ n
      · exact hSteps j hs
      · let terminal := (step^[n]) (initState x)
        have hFixed := (hStop x terminal result hResult).1
        have agrees : (step^[j]) (initState x) = terminal :=
          Fuel.iterate_after_fixed (used := n) rfl hFixed (by omega)
        rw [agrees]
        exact hSteps n le_rfl
    exact hWidth x _ fits.1 fits.2
  let computed := Fuel.boundedReachable startP stepP ticks width chanceWidth
  refine ⟨outputP.comp computed, ?_⟩
  intro x
  obtain ⟨result, n, hClock, hPost, hResult, _⟩ := evaluated x
  let terminal := (step^[n]) (initState x)
  have hFixed := hStop x terminal result hResult
  have agrees : (step^[ticks.eval (input x).length]) (initState x) = terminal :=
    Fuel.iterate_after_fixed (used := n) rfl hFixed.1 hClock
  change post x (output ((step^[ticks.eval (input x).length]) (initState x)))
  rw [agrees, hFixed.2]
  exact hPost

end WordDialogue
end EF1FPO
