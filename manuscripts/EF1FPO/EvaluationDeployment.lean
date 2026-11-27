import EF1FPO.EvaluatorProgram

/-! Deploy the rounded biased map evaluator as a closed bit program. -/

set_option autoImplicit false

namespace EF1FPO

open OAI.Optimization.LinearProgramming.OracleSpec

theorem evaluate_biased_binary : BitPolynomial EvaluationInput.encode EvaluationInput.output := by
  obtain ⟨M, C, degree, runs⟩ := bitPolynomial_of_procedure EvaluationWire.evaluationProcedure
  refine ⟨M, C, degree, fun d => ?_⟩
  obtain ⟨time, state, run, clock, stopped, transcript, output⟩ := runs d
  refine ⟨time, state, run, clock, stopped, transcript, ?_⟩
  rw [output]
  exact d.rounded_correct

end EF1FPO
