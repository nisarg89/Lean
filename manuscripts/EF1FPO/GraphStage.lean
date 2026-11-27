import EF1FPO.ClosedApproximation
import EF1FPO.GraphProgram

/-! Closed prepared-instance to greatest-weight mask procedure. -/

set_option autoImplicit false

namespace EF1FPO.GreatestGraphStage

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.Optimization.LinearProgramming.OracleSpec

noncomputable def chosenGuess (d : PreparedInput) : Guess :=
  Classical.choose (guess_exists d (ClosedApproximation.compute.output d)
    (ClosedApproximation.compute.correct d))

noncomputable def output (d : PreparedInput) : Word :=
  encodeBidderMask (chosenGuess d).mask

noncomputable def procedure :
    Procedure (fun d : PreparedInput => encodeInstance d.inst) id output := by
  exact composeRetainingInput ClosedApproximation.compute.procedure maskProcedure chosenGuess (fun d =>
    (Classical.choose_spec (guess_exists d (ClosedApproximation.compute.output d)
      (ClosedApproximation.compute.correct d))).2)

theorem output_correct (d : PreparedInput) :
    ∃ e : BidderMask d.inst, IsGreatestBidderMask d.inst e ∧ output d = encodeBidderMask e := by
  have transfer (g : Guess) (d' : PreparedInput) (h : g.prepared = d') :
      ∃ e : BidderMask d'.inst, IsGreatestBidderMask d'.inst e ∧
        encodeBidderMask g.mask = encodeBidderMask e := by
    subst d'
    exact ⟨g.mask, g.mask_correct, rfl⟩
  exact transfer (chosenGuess d) d
    (Classical.choose_spec (guess_exists d (ClosedApproximation.compute.output d)
      (ClosedApproximation.compute.correct d))).1

end EF1FPO.GreatestGraphStage
