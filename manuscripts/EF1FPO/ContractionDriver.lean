import EF1FPO.Controller
import EF1FPO.ControllerProcedure
import OAI.Optimization.LinearProgramming.OracleSpec.PriceUniform

/-! Compile the bounded, typed contraction controller to one finite bit program. -/

set_option autoImplicit false

namespace EF1FPO

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.Optimization.LinearProgramming.OracleSpec

noncomputable section

/-- The order-preserving contraction driver is a single bit program. Its clock includes
every evaluation query and reply bit. The cost to compute the oracle's answers is separate. -/
theorem monotone_contraction_approximation :
    ∃ (M : BitProgram) (C d : ℕ),
      ∀ (n b k : ℕ), 0 < n → ∀ (f : Vector n → Vector n) (v : Vector n)
        (reply : WordOracle), MonotoneContraction f b → unitCube v → f v = v →
        ApproximationOracle f reply →
        M.ComputesWithin reply (contractionInput n b k) (C * (n + b + k + 1) ^ d)
          (fun history output =>
            (∀ exchange ∈ history, ∃ (p s : ℕ) (a : GridNumerator n),
              unitCube (dyadicPoint p a) ∧ exchange.1 = dyadicQuery p s a) ∧
            ∃ (s : ℕ) (a : GridNumerator n), unitCube (dyadicPoint s a) ∧
              dist (dyadicPoint s a) v ≤ precisionError k ∧
              output = encodeUnary s ++ encodeGrid a) := by
  obtain ⟨width, count, sessions⟩ := BisectionDriver.bounded_session
  let dispatcher := BisectionDriver.procedure
  let perRound := dispatcher.shared.bound.comp width + Polynomial.C 18 * width + Polynomial.C 17
  let clock := count * perRound + Polynomial.C 3
  refine ⟨WordDialogue.machine dispatcher, clock.eval 1, clock.natDegree, ?_⟩
  intro n b k hn f v reply hContract hCube hFixed hOracle
  let input : BisectionDriver.Input := ⟨n, b, k, hn⟩
  let inputSize := n + b + k + 1
  obtain ⟨output, history, rounds, hRounds, session, hQueries, hOutput⟩ :=
    sessions input f v reply hContract hCube hFixed hOracle
  obtain ⟨elapsed, state, run, hElapsed, stopped, hResult⟩ :=
    WordDialogue.machine_computes dispatcher reply session
  have hClock : elapsed ≤ clock.eval inputSize := by
    calc
      elapsed ≤ rounds * (dispatcher.shared.bound.eval (width.eval inputSize) +
          18 * width.eval inputSize + 17) + 3 := hElapsed
      _ ≤ count.eval inputSize * (dispatcher.shared.bound.eval (width.eval inputSize) +
          18 * width.eval inputSize + 17) + 3 :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ hRounds) _
      _ = clock.eval inputSize := by
        simp only [clock, perRound, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_comp]
  refine ⟨elapsed, state, run,
    hClock.trans (eval_le_monomial clock inputSize (by dsimp [inputSize]; omega)), stopped, ?_⟩
  rw [hResult.1, hResult.2]
  exact ⟨hQueries, hOutput⟩

end

end EF1FPO
