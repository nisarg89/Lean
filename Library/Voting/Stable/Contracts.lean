import Voting.Contracts
import Voting.Stable.Basic

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable

namespace MetricDistortion.Contracts

namespace Model_DrawLaws

def Statement : Prop :=
∀ D : DrawLaw, (∀ k, 0 ≤ drawWeight D k) ∧ HasSum (drawWeight D) 1

end Model_DrawLaws



namespace Analysis_DrawSummability

def Statement : Prop :=
∀ D : DrawLaw, ∀ t ∈ Icc (0 : ℝ) 1,
  Summable (fun k => drawWeight D k*t^(k+1)) ∧
  (∀ k, drawWeight D k*t^(k+1) ∈ Icc (0 : ℝ) (drawWeight D k))

structure Needs : Prop where

  child_0 : Model_DrawLaws.Statement

end Analysis_DrawSummability



namespace Analysis_IntegralMixture

def Statement : Prop :=
∀ D : DrawLaw, ∀ b z : ℝ, 0 ≤ b → 0 ≤ z → b+z ≤ 1 →
  (∫ s in (0 : ℝ)..1, phi D (b+s*z)) =
    ∑' k, drawWeight D k*(∫ s in (0 : ℝ)..1, (b+s*z)^(k+1))

structure Needs : Prop where

  child_0 : Analysis_DrawSummability.Statement

end Analysis_IntegralMixture



namespace Analysis_GeneratingFunction

def Statement : Prop :=
∀ D : DrawLaw, MonotoneOn (phi D) (Icc (0 : ℝ) 1) ∧
  ConvexOn ℝ (Icc (0 : ℝ) 1) (phi D) ∧ ContinuousOn (phi D) (Icc (0 : ℝ) 1) ∧
  phi D 0 = 0 ∧ phi D 1 = 1 ∧ Phi D 1 = mu D ∧
  (D ≠ PMF.pure 0 → StrictConvexOn ℝ (Icc (0 : ℝ) 1) (phi D))

structure Needs : Prop where

  child_0 : Analysis_DrawSummability.Statement

  child_1 : Analysis_IntegralMixture.Statement

end Analysis_GeneratingFunction



namespace Comparison_ScoreRegularity

def Statement : Prop :=
∀ m D (r : Ranking m) c,
  ContinuousOn (fun p => ambientCompare D r p c) (simplex m) ∧
  ConvexOn ℝ (simplex m) (fun p => ambientCompare D r p c)

structure Needs : Prop where

  child_0 : Analysis_GeneratingFunction.Statement

  child_1 : Model_Lotteries.Statement

end Comparison_ScoreRegularity



namespace Comparison_ChallengerLinearity

def Statement : Prop :=
∀ n m D (σ : Profile n m) P β,
  (∀ c, score D σ P c ≤ β) ↔ (∀ A : Lottery m, payoff D σ A P ≤ β)

structure Needs : Prop where

  child_0 : Model_Lotteries.Statement

end Comparison_ChallengerLinearity



namespace Comparison_FixedDrawIntegral

def Statement : Prop :=
∀ m (r : Ranking m) (P : Lottery m) c k,
  fixedCompare r P c k = ∫ s in (0 : ℝ)..1, (below r P c+s*P.val c)^k

structure Needs : Prop where

  child_0 : Comparison_LabeledTie.Statement

  child_1 : Model_Lotteries.Statement

end Comparison_FixedDrawIntegral



namespace Comparison_Exchangeability

def Statement : Prop :=
∀ m (r : Ranking m) (P : Lottery m) k,
  (∑ c, P.val c*fixedCompare r P c k) = 1/(k+1 : ℕ)

structure Needs : Prop where

  child_0 : Comparison_FixedDrawIntegral.Statement

  child_1 : Model_RankIntervals.Statement

end Comparison_Exchangeability



namespace Comparison_CountableMixture

def Statement : Prop :=
∀ m D (r : Ranking m) (P : Lottery m) c,
  compare D r P c = ∑' k, drawWeight D k*(∫ s in (0 : ℝ)..1, (below r P c+s*P.val c)^(k+1))

structure Needs : Prop where

  child_0 : Comparison_FixedDrawIntegral.Statement

  child_1 : Analysis_IntegralMixture.Statement

end Comparison_CountableMixture



namespace Comparison_SelfPlay

def Statement : Prop :=
∀ n m, 0 < n → 0 < m → ∀ D (σ : Profile n m) P,
  payoff D σ P P = mu D

structure Needs : Prop where

  child_0 : Comparison_Exchangeability.Statement

  child_1 : Comparison_CountableMixture.Statement

end Comparison_SelfPlay



namespace Comparison_AffineSubstitution

def Statement : Prop :=
∀ D : DrawLaw, ∀ b z : ℝ, 0 ≤ b → 0 < z → b+z ≤ 1 →
  (∫ s in (0 : ℝ)..1, phi D (b+s*z)) = (∫ u in b..(b+z), phi D u)/z

structure Needs : Prop where

  child_0 : Analysis_GeneratingFunction.Statement

end Comparison_AffineSubstitution



namespace Comparison_CandidateDraws

def Statement : Prop :=
∀ m (D : DrawLaw) (r : Ranking m) (P : Lottery m) c,
  compare D r P c = ambientCompare D r P.val c ∧
  (0 < P.val c → compare D r P c =
    (∫ u in below r P c..(below r P c + P.val c), phi D u) / P.val c) ∧
  ContinuousOn (fun p => ambientCompare D r p c) (simplex m) ∧
  ConvexOn ℝ (simplex m) (fun p => ambientCompare D r p c)

structure Needs : Prop where

  child_0 : Comparison_FixedDrawIntegral.Statement

  child_1 : Comparison_CountableMixture.Statement

  child_2 : Comparison_ScoreRegularity.Statement

  child_3 : Comparison_AffineSubstitution.Statement

  child_4 : Analysis_IntegralMixture.Statement

end Comparison_CandidateDraws



namespace Stability_MinimaxApplication

def Statement : Prop :=
∀ n m, 0 < n → 0 < m → ∀ D (σ : Profile n m), ∃ P, Stable D σ P

structure Needs : Prop where

  child_0 : Shared_CompactConvexMinimax.Statement

  child_1 : Comparison_ScoreRegularity.Statement

  child_2 : Comparison_ChallengerLinearity.Statement

  child_3 : Comparison_SelfPlay.Statement

  child_4 : Comparison_CandidateDraws.Statement

end Stability_MinimaxApplication



namespace Stability_SupportEquality

def Statement : Prop :=
∀ n m, 0 < n → 0 < m → ∀ D (σ : Profile n m) P,
  Stable D σ P → ∀ c, 0 < P.val c → score D σ P c = mu D

structure Needs : Prop where

  child_0 : Comparison_SelfPlay.Statement

  child_1 : Model_Lotteries.Statement

end Stability_SupportEquality



namespace Stability_Existence

def Statement : Prop :=
(∀ n m, 0 < n → 0 < m → ∀ (σ : Profile n m) D,
  ∃ P, Stable D σ P) ∧
  (∀ n m, 0 < n → 0 < m → ∀ (σ : Profile n m) D P,
    Stable D σ P → ∀ c, 0 < P.val c → score D σ P c = mu D) ∧
  (∀ D : DrawLaw, ∀ β : ℝ, β < mu D → ∃ n m, 0 < n ∧ 0 < m ∧
    ∃ σ : Profile n m, ∀ P : Lottery m, ∃ c, β < score D σ P c)

structure Needs : Prop where

  child_0 : Stability_MinimaxApplication.Statement

  child_1 : Comparison_SelfPlay.Statement

  child_2 : Stability_SupportEquality.Statement

end Stability_Existence



namespace Geometry_Rearrangement

def Statement : Prop :=
∀ D : DrawLaw, ∀ a p A : ℝ, 0 ≤ a → a ≤ p → p ≤ A → A ≤ 1 →
  ∀ S : Set ℝ, MeasurableSet S → S ⊆ Icc 0 A → volume S = ENNReal.ofReal p →
  (∀ᵐ u ∂volume, u ∈ Icc 0 a → u ∈ S) →
  (∫ u in S, (phi D u-mu D)) ≤ Phi D a+Phi D A-Phi D (a+A-p)-p*mu D

structure Needs : Prop where

  child_0 : Analysis_MonotoneSetIntegral.Statement

  child_1 : Analysis_GeneratingFunction.Statement

end Geometry_Rearrangement



namespace Geometry_ApproximateCancellation

def Statement : Prop :=
∀ n m, 0 < n → 0 < m → ∀ D (σ : Profile n m) P δ,
  0 ≤ δ → ApproxStable D σ P δ → ∀ H o,
  -δ*(1-mass P H) ≤ avg (fun v => ∫ u in region (σ v) P H, (phi D u-mu D)) ∧
  avg (fun v => phi D (below (σ v) P o)) ≤ mu D+δ

structure Needs : Prop where

  child_0 : Comparison_SelfPlay.Statement

  child_1 : Comparison_CandidateDraws.Statement

  child_2 : Model_RankIntervals.Statement

  child_3 : Analysis_GeneratingFunction.Statement

end Geometry_ApproximateCancellation



namespace Geometry_RankStability

def Statement : Prop :=
∀ n m, 0 < n → 0 < m → ∀ D (σ : Profile n m) P,
  Stable D σ P → ∀ H o,
  avg (fun v => ∫ u in region (σ v) P H, (phi D u-mu D)) = 0 ∧
  avg (fun v => phi D (below (σ v) P o)) ≤ mu D

structure Needs : Prop where

  child_0 : Stability_SupportEquality.Statement

  child_1 : Comparison_CandidateDraws.Statement

  child_2 : Model_RankIntervals.Statement

  child_3 : Analysis_GeneratingFunction.Statement

end Geometry_RankStability



namespace Comparison_FixedDrawSpecialization

def Statement : Prop :=
∀ n m (σ : Profile n m) P c k,
  score (PMF.pure k) σ P c = avg (fun v => fixedCompare (σ v) P c (k+1))

structure Needs : Prop where

  child_0 : Model_DrawLaws.Statement

end Comparison_FixedDrawSpecialization



namespace Comparison_MaximalLottery

def Statement : Prop :=
∀ n m, 0 < n → 0 < m → ∀ (σ : Profile n m) P,
  Stable (PMF.pure 0) σ P ↔
  ∀ c, avg (fun v => below (σ v) P c)+P.val c/2 ≤ 1/2

structure Needs : Prop where

  child_0 : Comparison_FixedDrawSpecialization.Statement

  child_1 : Comparison_FixedDrawIntegral.Statement

end Comparison_MaximalLottery



end MetricDistortion.Contracts
