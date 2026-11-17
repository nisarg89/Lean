import Voting
import Voting.Stable.Certificate

/-! Random-size stable lotteries for arbitrary positive draw-count laws. -/
noncomputable section
namespace Voting.Stable

/-- A draw law on positive integers: index `k` represents `k+1` draws. -/
abbrev DrawLaw := MetricDistortion.DrawLaw
/-- The comparison score's common benchmark. -/
abbrev benchmark (law : DrawLaw) : ℝ := MetricDistortion.mu law
/-- Candidate comparison score against the lottery. -/
abbrev score {n m : ℕ} (law : DrawLaw) (profile : Voting.Profile n m)
    (lottery : Voting.Lottery m) (candidate : Fin m) : ℝ :=
  MetricDistortion.score law profile lottery candidate
/-- A random-size stable lottery for the given law and profile. -/
abbrev IsStable {n m : ℕ} (law : DrawLaw) (profile : Voting.Profile n m)
    (lottery : Voting.Lottery m) : Prop := MetricDistortion.Stable law profile lottery
/-- Stability up to an additive score error. -/
abbrev IsApproxStable {n m : ℕ} (law : DrawLaw) (profile : Voting.Profile n m)
    (lottery : Voting.Lottery m) (error : ℝ) : Prop :=
  MetricDistortion.ApproxStable law profile lottery error
/-- A stable lottery exists for each law and nonempty finite profile. -/
theorem exists_stable {n m : ℕ} (voters : 0 < n) (candidates : 0 < m)
    (profile : Voting.Profile n m) (law : DrawLaw) :
    ∃ lottery : Voting.Lottery m, IsStable law profile lottery :=
  MetricDistortion.Certified.Stability_Existence.1 n m voters candidates profile law
/-- Every positive-weight candidate in a stable lottery attains the benchmark. -/
theorem support_score_eq {n m : ℕ} (voters : 0 < n) (candidates : 0 < m)
    (profile : Voting.Profile n m) (law : DrawLaw) (lottery : Voting.Lottery m)
    (stable : IsStable law profile lottery) (candidate : Fin m)
    (positive : 0 < lottery.val candidate) : score law profile lottery candidate = benchmark law :=
  MetricDistortion.Certified.Stability_Existence.2.1 n m voters candidates profile law
    lottery stable candidate positive
/-- One-draw stability is equivalent to the maximal-lottery inequalities. -/
theorem maximal_lottery_iff {n m : ℕ} (voters : 0 < n) (candidates : 0 < m)
    (profile : Voting.Profile n m) (lottery : Voting.Lottery m) :
    IsStable (PMF.pure 0) profile lottery ↔
      ∀ c, MetricDistortion.avg (fun v => Voting.below (profile v) lottery c) +
        lottery.val c / 2 ≤ 1 / 2 :=
  MetricDistortion.Certified.Comparison_MaximalLottery n m voters candidates profile lottery
/-- The complete candidate-comparison formula and its regularity properties. -/
theorem comparison_formula : MetricDistortion.Contracts.Comparison_CandidateDraws.Statement :=
  MetricDistortion.Certified.Comparison_CandidateDraws
/-- The complete rank-stability cancellation and rank bound. -/
theorem rank_stability : MetricDistortion.Contracts.Geometry_RankStability.Statement :=
  MetricDistortion.Certified.Geometry_RankStability
end Voting.Stable
