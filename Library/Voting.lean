import Voting.Certificate

/-! Finite strict rankings, profiles and candidate lotteries. -/
noncomputable section
namespace Voting

/-- A strict ranking of `m` candidates. Higher values are more preferred. -/
abbrev Ranking (m : ℕ) := MetricDistortion.Ranking m
/-- A finite profile of `n` strict rankings over `m` candidates. -/
abbrev Profile (n m : ℕ) := MetricDistortion.Profile n m
/-- A nonnegative real-valued probability vector on the candidates. -/
abbrev Lottery (m : ℕ) := MetricDistortion.Lottery m
/-- A profile-dependent rule returning a lottery for each nonempty profile. -/
abbrev Rule := MetricDistortion.VotingRule
/-- Strict preference within a ranking. -/
abbrev prefers {m : ℕ} (ranking : Ranking m) (a b : Fin m) : Prop :=
  MetricDistortion.prefers ranking a b
/-- Probability assigned to a candidate set. -/
abbrev mass {m : ℕ} (lottery : Lottery m) (candidates : Set (Fin m)) : ℝ :=
  MetricDistortion.mass lottery candidates
/-- Lottery mass strictly below a candidate in a ranking. -/
abbrev below {m : ℕ} (ranking : Ranking m) (lottery : Lottery m) (c : Fin m) : ℝ :=
  MetricDistortion.below ranking lottery c
end Voting
