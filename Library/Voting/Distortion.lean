import Voting.Stable
import Voting.Distortion.Certificate

/-!
General metric-distortion bounds for random-size stable lotteries.

Provide an `UpperBoundCertificate` for the draw law, then apply
`distortion_le_of_certificate` to any stable lottery. Alternatively,
`exists_stable_with_distortion_bound` supplies such a lottery for each nonempty
profile. `approx_cost_bound` gives the accompanying approximate-stability result.

The certificate uses the rank-cut witness internally. Its current witness format has
exactly nine indexed components; arbitrary positive-integer draw laws are supported.
-/

noncomputable section
open scoped ENNReal

namespace Voting.Distortion

/-- A strict preference profile with `n` voters and `m` candidates. -/
abbrev Profile (n m : ℕ) := MetricDistortion.Profile n m

/-- A probability distribution over the candidates. -/
abbrev Lottery (m : ℕ) := MetricDistortion.Lottery m

/-- A probability distribution over positive draw counts, indexed from zero. -/
abbrev DrawLaw := MetricDistortion.DrawLaw

/-- Parameters witnessing a rank-cut distortion bound. -/
abbrev CutWitness := MetricDistortion.CutParameters

/-- The random-size stability condition for a profile and lottery. -/
abbrev Stable {n m : ℕ} (law : DrawLaw) (profile : Profile n m) (lottery : Lottery m) : Prop :=
  MetricDistortion.Stable law profile lottery

/-- The approximate random-size stability condition. -/
abbrev ApproxStable {n m : ℕ} (law : DrawLaw) (profile : Profile n m)
    (lottery : Lottery m) (error : ℝ) : Prop :=
  MetricDistortion.ApproxStable law profile lottery error

/-- A witness satisfies the rank-cut criterion for the given draw law. -/
abbrev ValidCut (law : DrawLaw) (witness : CutWitness) : Prop :=
  MetricDistortion.ValidCut law witness

/-- Worst-case distortion over metrics consistent with a profile. -/
abbrev distortion {n m : ℕ} (profile : Profile n m) (lottery : Lottery m) : ℝ≥0∞ :=
  MetricDistortion.distortion profile lottery

/-- The complete rank-cut criterion, including approximate stability. -/
abbrev RankCutCriterion : Prop := MetricDistortion.Contracts.Geometry_RankCutCriterion.Statement

/-- A random-size stable lottery exists for every finite nonempty profile and draw law. -/
theorem stable_exists {n m : ℕ} (voters : 0 < n) (candidates : 0 < m)
    (profile : Profile n m) (law : DrawLaw) :
    ∃ lottery : Lottery m, Stable law profile lottery :=
  MetricDistortion.Certified.Stability_Existence.1 n m voters candidates profile law

/-- A valid rank-cut witness bounds the distortion of any stable lottery. -/
theorem rank_cut_bound (law : DrawLaw) (witness : CutWitness)
    (valid : ValidCut law witness) {n m : ℕ}
    (voters : 0 < n) (candidates : 0 < m) (profile : Profile n m)
    (lottery : Lottery m) (stable : Stable law profile lottery) :
    distortion profile lottery ≤ ENNReal.ofReal (1 + 2 * witness.C0) :=
  (MetricDistortion.Certified.Geometry_RankCutCriterion law witness valid).1
    n m voters candidates profile lottery stable

/-- The full rank-cut criterion, including its approximate-stability bound. -/
theorem rank_cut_criterion : RankCutCriterion :=
  MetricDistortion.Certified.Geometry_RankCutCriterion

/-- A verified upper-bound certificate for a random-size draw law.

A certificate packages rank-cut witness data together with a proof that the data
satisfy the general cut conditions. The current witness has nine indexed components.
-/
structure UpperBoundCertificate (law : DrawLaw) where
  /-- The witness data used to establish the bound. -/
  witness : CutWitness
  /-- Proof that the witness is valid for the given draw law. -/
  valid : ValidCut law witness

/-- Distortion bound computed from a valid upper-bound certificate. -/
def UpperBoundCertificate.bound {law : DrawLaw} (certificate : UpperBoundCertificate law) : ℝ :=
  1 + 2 * certificate.witness.C0

/-- Every stable lottery obeys the bound of its supplied certificate. -/
theorem distortion_le_of_certificate (law : DrawLaw)
    (certificate : UpperBoundCertificate law) {n m : ℕ}
    (voters : 0 < n) (candidates : 0 < m) (profile : Profile n m)
    (lottery : Lottery m) (stable : Stable law profile lottery) :
    distortion profile lottery ≤ ENNReal.ofReal certificate.bound :=
  rank_cut_bound law certificate.witness certificate.valid voters candidates profile lottery stable

/-- Each nonempty profile has a stable lottery obeying a supplied certificate's bound. -/
theorem exists_stable_with_distortion_bound (law : DrawLaw)
    (certificate : UpperBoundCertificate law) {n m : ℕ}
    (voters : 0 < n) (candidates : 0 < m) (profile : Profile n m) :
    ∃ lottery : Lottery m, Stable law profile lottery ∧
      distortion profile lottery ≤ ENNReal.ofReal certificate.bound := by
  obtain ⟨lottery, stable⟩ := stable_exists voters candidates profile law
  exact ⟨lottery, stable,
    distortion_le_of_certificate law certificate voters candidates profile lottery stable⟩

/-- The additional local condition used to bound an approximately stable lottery. -/
def ApproximationCertificate {law : DrawLaw} (certificate : UpperBoundCertificate law)
    (B : ℝ) : Prop :=
  ∀ p ∈ Set.Icc (0 : ℝ) 1,
    (1 - p) * certificate.witness.lambda p + certificate.witness.tau 0 p ≤ B

/-- Approximate stability controls cost up to the displayed additive error term. -/
theorem approx_cost_bound (law : DrawLaw) (certificate : UpperBoundCertificate law)
    (B : ℝ) (approximation : ApproximationCertificate certificate B)
    {n m : ℕ} (voters : 0 < n) (candidates : 0 < m) (profile : Profile n m)
    (lottery : Lottery m) (δ : ℝ) (error_nonneg : 0 ≤ δ)
    (approx_stable : ApproxStable law profile lottery δ)
    (metric : MetricDistortion.Metric n m) (consistent : MetricDistortion.Consistent profile metric)
    (optimal : Fin m) (is_optimal : MetricDistortion.Optimal metric optimal) :
    MetricDistortion.expectedCost metric lottery ≤
      certificate.bound * MetricDistortion.sc metric optimal +
      B * δ * sSup (Set.range fun c => MetricDistortion.distance metric (.inr optimal) (.inr c)) :=
  (MetricDistortion.Certified.Geometry_RankCutCriterion law certificate.witness
    certificate.valid).2 B approximation n m voters candidates profile lottery δ
    error_nonneg approx_stable metric consistent optimal is_optimal

end Voting.Distortion
