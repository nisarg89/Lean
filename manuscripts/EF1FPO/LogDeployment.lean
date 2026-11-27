import EF1FPO.LogProgram

/-! Deploy the uniform rational logarithm procedure as a closed bit program. -/

set_option autoImplicit false

namespace EF1FPO

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.Optimization.LinearProgramming.OracleSpec

theorem evaluate_log_binary : BitPolynomial encodeLogInput logOutput := by
  obtain ⟨M, C, degree, hRun⟩ := bitPolynomial_of_procedure evaluateLogProcedure
  refine ⟨M, C, degree, fun d => ?_⟩
  obtain ⟨time, state, run, clock, stopped, history, output⟩ := hRun d
  exact ⟨time, state, run, clock, stopped, history, logApproximation d,
    logApproximation_correct d, output⟩

end EF1FPO
