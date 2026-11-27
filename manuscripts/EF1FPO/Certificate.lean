import EF1FPO.Algorithm
import EF1FPO.ContractionDriver
import EF1FPO.LogDeployment
import EF1FPO.EvaluationDeployment
import EF1FPO.GraphDeployment
import EF1FPO.Pipeline
import EF1FPO.StructuredClosure

/-! Contract for the manuscript's deterministic binary-polynomial main theorem. -/

namespace EF1FPO

/-- One fixed deterministic finite-alphabet program returns a complete EF1 and fPO
allocation at the original rational valuations, with one polynomial in the full binary input. -/
theorem ef1_fpo_polynomial : BitPolynomial encodeInstance (fun I bits =>
    ∃ A : I.Allocation, I.IsEF1 A ∧ I.IsFPO A ∧ bits = encodeAllocation A) := by
  let certified := Pipeline.composed
  obtain ⟨M, C, degree, hRun⟩ := bitPolynomial_of_procedure certified.procedure
  refine ⟨M, C, degree, fun I => ?_⟩
  obtain ⟨A, hEF1, hFPO, hWord⟩ := certified.correct I
  obtain ⟨time, config, run, clock, stopped, history, output⟩ := hRun I
  exact ⟨time, config, run, clock, stopped, history, A, hEF1, hFPO, output.trans hWord⟩

end EF1FPO
