import EF1FPO.Computation
import OAI.Optimization.LinearProgramming.OracleSpec.BitStackDeployment
import OAI.Optimization.LinearProgramming.OracleSpec.PriceUniform

/-! Deployment of a polynomial stack procedure as a closed binary machine. -/

set_option autoImplicit false

namespace EF1FPO

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.Optimization.LinearProgramming.OracleSpec

theorem bitPolynomial_of_procedure {X : Type} {input : X → Word} {output : X → Word}
    (program : Procedure input id output) :
    BitPolynomial input (fun x bits => bits = output x) := by
  let clock : Polynomial ℕ := Polynomial.C 3 * program.bound + Polynomial.C 2 * Polynomial.X + Polynomial.C 2
  refine ⟨BitCode.deploy program, clock.eval 1, clock.natDegree, fun x => ?_⟩
  obtain ⟨elapsed, final, trace, hElapsed, stopped, result⟩ :=
    BitCode.deploy_correct program (fun _ _ => []) x
  refine ⟨elapsed, final, trace, ?_, stopped, result⟩
  have hClock : elapsed ≤ clock.eval (input x).length := by
    simpa only [clock, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using hElapsed
  exact hClock.trans ((Procedure.eval_nat_mono clock (Nat.le_succ _)).trans
    (eval_le_monomial clock _ (Nat.succ_pos _)))

end EF1FPO
