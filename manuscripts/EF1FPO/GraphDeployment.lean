import EF1FPO.GraphStage

/-! Deploy both closed computation stages on the prepared table wire. -/

set_option autoImplicit false

namespace EF1FPO

open OAI.Optimization.LinearProgramming.OracleSpec

theorem approximate_biased_binary :
    BitPolynomial (fun d : PreparedInput => encodeInstance d.inst) approximateOutput := by
  let solver := ClosedApproximation.compute
  obtain ⟨M, C, degree, runs⟩ := bitPolynomial_of_procedure solver.procedure
  refine ⟨M, C, degree, fun d => ?_⟩
  obtain ⟨time, state, run, clock, stopped, history, output⟩ := runs d
  refine ⟨time, state, run, clock, stopped, history, ?_⟩
  rw [output]
  exact solver.correct d

theorem identify_greatest_graph_binary :
    BitPolynomial (fun d : PreparedInput => encodeInstance d.inst) (fun d bits =>
      ∃ e : BidderMask d.inst, IsGreatestBidderMask d.inst e ∧ bits = encodeBidderMask e) := by
  obtain ⟨M, C, degree, runs⟩ := bitPolynomial_of_procedure GreatestGraphStage.procedure
  refine ⟨M, C, degree, fun d => ?_⟩
  obtain ⟨time, state, run, clock, stopped, history, output⟩ := runs d
  refine ⟨time, state, run, clock, stopped, history, ?_⟩
  rw [output]
  exact GreatestGraphStage.output_correct d

end EF1FPO
