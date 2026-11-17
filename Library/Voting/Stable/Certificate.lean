import Voting.Certificate
import Voting.Stable.Analysis.DrawSummability
import Voting.Stable.Analysis.GeneratingFunction
import Voting.Stable.Analysis.IntegralMixture
import Voting.Stable.ApproximateCancellation
import Voting.Stable.Comparison.AffineSubstitution
import Voting.Stable.Comparison.CandidateDraws
import Voting.Stable.Comparison.ChallengerLinearity
import Voting.Stable.Comparison.CountableMixture
import Voting.Stable.Comparison.Exchangeability
import Voting.Stable.Comparison.FixedDrawIntegral
import Voting.Stable.Comparison.FixedDrawSpecialization
import Voting.Stable.Comparison.MaximalLottery
import Voting.Stable.Comparison.ScoreRegularity
import Voting.Stable.Comparison.SelfPlay
import Voting.Stable.DrawLaws
import Voting.Stable.Existence
import Voting.Stable.MinimaxApplication
import Voting.Stable.RankStability
import Voting.Stable.Rearrangement
import Voting.Stable.SupportEquality

noncomputable section
namespace MetricDistortion.Certified

theorem Model_DrawLaws : MetricDistortion.Contracts.Model_DrawLaws.Statement := MetricDistortion.Contracts.Model_DrawLaws.proved
theorem Analysis_DrawSummability : MetricDistortion.Contracts.Analysis_DrawSummability.Statement := MetricDistortion.Contracts.Analysis_DrawSummability.from_children {child_0 := Model_DrawLaws}
theorem Analysis_IntegralMixture : MetricDistortion.Contracts.Analysis_IntegralMixture.Statement := MetricDistortion.Contracts.Analysis_IntegralMixture.from_children {child_0 := Analysis_DrawSummability}
theorem Analysis_GeneratingFunction : MetricDistortion.Contracts.Analysis_GeneratingFunction.Statement := MetricDistortion.Contracts.Analysis_GeneratingFunction.from_children {child_0 := Analysis_DrawSummability, child_1 := Analysis_IntegralMixture}
theorem Comparison_ScoreRegularity : MetricDistortion.Contracts.Comparison_ScoreRegularity.Statement := MetricDistortion.Contracts.Comparison_ScoreRegularity.from_children {child_0 := Analysis_GeneratingFunction, child_1 := Model_Lotteries}
theorem Comparison_ChallengerLinearity : MetricDistortion.Contracts.Comparison_ChallengerLinearity.Statement := MetricDistortion.Contracts.Comparison_ChallengerLinearity.from_children {child_0 := Model_Lotteries}
theorem Comparison_FixedDrawIntegral : MetricDistortion.Contracts.Comparison_FixedDrawIntegral.Statement := MetricDistortion.Contracts.Comparison_FixedDrawIntegral.from_children {child_0 := Comparison_LabeledTie, child_1 := Model_Lotteries}
theorem Comparison_Exchangeability : MetricDistortion.Contracts.Comparison_Exchangeability.Statement := MetricDistortion.Contracts.Comparison_Exchangeability.from_children {child_0 := Comparison_FixedDrawIntegral, child_1 := Model_RankIntervals}
theorem Comparison_CountableMixture : MetricDistortion.Contracts.Comparison_CountableMixture.Statement := MetricDistortion.Contracts.Comparison_CountableMixture.from_children {child_0 := Comparison_FixedDrawIntegral, child_1 := Analysis_IntegralMixture}
theorem Comparison_SelfPlay : MetricDistortion.Contracts.Comparison_SelfPlay.Statement := MetricDistortion.Contracts.Comparison_SelfPlay.from_children {child_0 := Comparison_Exchangeability, child_1 := Comparison_CountableMixture}
theorem Comparison_AffineSubstitution : MetricDistortion.Contracts.Comparison_AffineSubstitution.Statement := MetricDistortion.Contracts.Comparison_AffineSubstitution.from_children {child_0 := Analysis_GeneratingFunction}
theorem Comparison_CandidateDraws : MetricDistortion.Contracts.Comparison_CandidateDraws.Statement := MetricDistortion.Contracts.Comparison_CandidateDraws.from_children {child_0 := Comparison_FixedDrawIntegral, child_1 := Comparison_CountableMixture, child_2 := Comparison_ScoreRegularity, child_3 := Comparison_AffineSubstitution, child_4 := Analysis_IntegralMixture}
theorem Stability_MinimaxApplication : MetricDistortion.Contracts.Stability_MinimaxApplication.Statement := MetricDistortion.Contracts.Stability_MinimaxApplication.from_children {child_0 := Shared_CompactConvexMinimax, child_1 := Comparison_ScoreRegularity, child_2 := Comparison_ChallengerLinearity, child_3 := Comparison_SelfPlay, child_4 := Comparison_CandidateDraws}
theorem Stability_SupportEquality : MetricDistortion.Contracts.Stability_SupportEquality.Statement := MetricDistortion.Contracts.Stability_SupportEquality.from_children {child_0 := Comparison_SelfPlay, child_1 := Model_Lotteries}
theorem Stability_Existence : MetricDistortion.Contracts.Stability_Existence.Statement := MetricDistortion.Contracts.Stability_Existence.from_children {child_0 := Stability_MinimaxApplication, child_1 := Comparison_SelfPlay, child_2 := Stability_SupportEquality}
theorem Geometry_Rearrangement : MetricDistortion.Contracts.Geometry_Rearrangement.Statement := MetricDistortion.Contracts.Geometry_Rearrangement.from_children {child_0 := Analysis_MonotoneSetIntegral, child_1 := Analysis_GeneratingFunction}
theorem Geometry_ApproximateCancellation : MetricDistortion.Contracts.Geometry_ApproximateCancellation.Statement := MetricDistortion.Contracts.Geometry_ApproximateCancellation.from_children {child_0 := Comparison_SelfPlay, child_1 := Comparison_CandidateDraws, child_2 := Model_RankIntervals, child_3 := Analysis_GeneratingFunction}
theorem Geometry_RankStability : MetricDistortion.Contracts.Geometry_RankStability.Statement := MetricDistortion.Contracts.Geometry_RankStability.from_children {child_0 := Stability_SupportEquality, child_1 := Comparison_CandidateDraws, child_2 := Model_RankIntervals, child_3 := Analysis_GeneratingFunction}
theorem Comparison_FixedDrawSpecialization : MetricDistortion.Contracts.Comparison_FixedDrawSpecialization.Statement := MetricDistortion.Contracts.Comparison_FixedDrawSpecialization.from_children {child_0 := Model_DrawLaws}
theorem Comparison_MaximalLottery : MetricDistortion.Contracts.Comparison_MaximalLottery.Statement := MetricDistortion.Contracts.Comparison_MaximalLottery.from_children {child_0 := Comparison_FixedDrawSpecialization, child_1 := Comparison_FixedDrawIntegral}

end MetricDistortion.Certified
