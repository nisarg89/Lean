import Voting.Math.CompactConvexMinimax
import Voting.Math.MonotoneSetIntegral
import Voting.Model.Lotteries
import Voting.Model.Profiles
import Voting.Model.RankIntervals
import Voting.Probability.LabeledTie
import Voting.Probability.PowerIntegral

noncomputable section
namespace MetricDistortion.Certified

theorem Shared_CompactConvexMinimax : MetricDistortion.Contracts.Shared_CompactConvexMinimax.Statement := MetricDistortion.Contracts.Shared_CompactConvexMinimax.proved
theorem Model_Lotteries : MetricDistortion.Contracts.Model_Lotteries.Statement := MetricDistortion.Contracts.Model_Lotteries.proved
theorem Comparison_PowerIntegral : MetricDistortion.Contracts.Comparison_PowerIntegral.Statement := MetricDistortion.Contracts.Comparison_PowerIntegral.proved
theorem Comparison_LabeledTie : MetricDistortion.Contracts.Comparison_LabeledTie.Statement := MetricDistortion.Contracts.Comparison_LabeledTie.from_children {child_0 := Comparison_PowerIntegral}
theorem Model_Profiles : MetricDistortion.Contracts.Model_Profiles.Statement := MetricDistortion.Contracts.Model_Profiles.proved
theorem Model_RankIntervals : MetricDistortion.Contracts.Model_RankIntervals.Statement := MetricDistortion.Contracts.Model_RankIntervals.from_children {child_0 := Model_Profiles, child_1 := Model_Lotteries}
theorem Analysis_MonotoneSetIntegral : MetricDistortion.Contracts.Analysis_MonotoneSetIntegral.Statement := MetricDistortion.Contracts.Analysis_MonotoneSetIntegral.proved

end MetricDistortion.Certified
