import Voting.Distortion.Geometry.AverageAndDistortion
import Voting.Distortion.Geometry.CommonCharge
import Voting.Distortion.Geometry.CrossingDiameter
import Voting.Distortion.Geometry.CrossingMeasure
import Voting.Distortion.Geometry.CutoffProperties
import Voting.Distortion.Geometry.IntegratedLocalCut
import Voting.Distortion.Geometry.MetricRankCuts
import Voting.Distortion.Geometry.MetricTail
import Voting.Distortion.Geometry.RankCutCriterion
import Voting.Distortion.Geometry.ThresholdStepFunctions
import Voting.Distortion.Model.DistortionConventions
import Voting.Distortion.Model.Metrics
import Voting.Distortion.Model.OffsetDefinitions
import Voting.Distortion.Offsets.BipartiteExtension
import Voting.Distortion.Offsets.CrossDistanceProperties
import Voting.Distortion.Offsets.MetricDomination
import Voting.Distortion.Offsets.MetricRealization
import Voting.Distortion.Offsets.ReductionToOffsets
import Voting.Stable.Certificate

noncomputable section
namespace MetricDistortion.Certified

theorem Model_Metrics : MetricDistortion.Contracts.Model_Metrics.Statement := MetricDistortion.Contracts.Model_Metrics.proved
theorem Geometry_CutoffProperties : MetricDistortion.Contracts.Geometry_CutoffProperties.Statement := MetricDistortion.Contracts.Geometry_CutoffProperties.from_children {child_0 := Model_RankIntervals, child_1 := Model_Metrics}
theorem Geometry_ThresholdStepFunctions : MetricDistortion.Contracts.Geometry_ThresholdStepFunctions.Statement := MetricDistortion.Contracts.Geometry_ThresholdStepFunctions.from_children {child_0 := Geometry_CutoffProperties}
theorem Geometry_MetricTail : MetricDistortion.Contracts.Geometry_MetricTail.Statement := MetricDistortion.Contracts.Geometry_MetricTail.from_children {child_0 := Geometry_CutoffProperties, child_1 := Geometry_ThresholdStepFunctions, child_2 := Model_Metrics}
theorem Geometry_CrossingDiameter : MetricDistortion.Contracts.Geometry_CrossingDiameter.Statement := MetricDistortion.Contracts.Geometry_CrossingDiameter.from_children {child_0 := Geometry_CutoffProperties, child_1 := Model_Metrics}
theorem Geometry_CrossingMeasure : MetricDistortion.Contracts.Geometry_CrossingMeasure.Statement := MetricDistortion.Contracts.Geometry_CrossingMeasure.from_children {child_0 := Geometry_CrossingDiameter, child_1 := Geometry_ThresholdStepFunctions}
theorem Geometry_MetricRankCuts : MetricDistortion.Contracts.Geometry_MetricRankCuts.Statement := MetricDistortion.Contracts.Geometry_MetricRankCuts.from_children {child_0 := Geometry_MetricTail, child_1 := Geometry_CrossingDiameter, child_2 := Geometry_CrossingMeasure}
theorem Geometry_IntegratedLocalCut : MetricDistortion.Contracts.Geometry_IntegratedLocalCut.Statement := MetricDistortion.Contracts.Geometry_IntegratedLocalCut.from_children {child_0 := Geometry_Rearrangement, child_1 := Geometry_MetricRankCuts, child_2 := Geometry_ThresholdStepFunctions, child_3 := Geometry_CutoffProperties, child_4 := Model_RankIntervals}
theorem Geometry_CommonCharge : MetricDistortion.Contracts.Geometry_CommonCharge.Statement := MetricDistortion.Contracts.Geometry_CommonCharge.from_children {child_0 := Analysis_GeneratingFunction}
theorem Model_DistortionConventions : MetricDistortion.Contracts.Model_DistortionConventions.Statement := MetricDistortion.Contracts.Model_DistortionConventions.proved
theorem Geometry_AverageAndDistortion : MetricDistortion.Contracts.Geometry_AverageAndDistortion.Statement := MetricDistortion.Contracts.Geometry_AverageAndDistortion.from_children {child_0 := Model_DistortionConventions, child_1 := Model_Metrics}
theorem Geometry_RankCutCriterion : MetricDistortion.Contracts.Geometry_RankCutCriterion.Statement := MetricDistortion.Contracts.Geometry_RankCutCriterion.from_children {child_0 := Geometry_IntegratedLocalCut, child_1 := Geometry_CommonCharge, child_2 := Geometry_ApproximateCancellation, child_3 := Geometry_AverageAndDistortion, child_4 := Geometry_ThresholdStepFunctions, child_5 := Geometry_MetricTail}
theorem Offsets_BipartiteExtension : MetricDistortion.Contracts.Offsets_BipartiteExtension.Statement := MetricDistortion.Contracts.Offsets_BipartiteExtension.from_children {child_0 := Model_Metrics}
theorem Model_OffsetDefinitions : MetricDistortion.Contracts.Model_OffsetDefinitions.Statement := MetricDistortion.Contracts.Model_OffsetDefinitions.proved
theorem Offsets_CrossDistanceProperties : MetricDistortion.Contracts.Offsets_CrossDistanceProperties.Statement := MetricDistortion.Contracts.Offsets_CrossDistanceProperties.from_children {child_0 := Model_OffsetDefinitions}
theorem Offsets_MetricRealization : MetricDistortion.Contracts.Offsets_MetricRealization.Statement := MetricDistortion.Contracts.Offsets_MetricRealization.from_children {child_0 := Offsets_BipartiteExtension, child_1 := Offsets_CrossDistanceProperties, child_2 := Model_OffsetDefinitions, child_3 := Model_DistortionConventions}
theorem Offsets_MetricDomination : MetricDistortion.Contracts.Offsets_MetricDomination.Statement := MetricDistortion.Contracts.Offsets_MetricDomination.from_children {child_0 := Model_OffsetDefinitions, child_1 := Model_Metrics}
theorem Offsets_ReductionToOffsets : MetricDistortion.Contracts.Offsets_ReductionToOffsets.Statement := MetricDistortion.Contracts.Offsets_ReductionToOffsets.from_children {child_0 := Offsets_MetricRealization, child_1 := Offsets_MetricDomination, child_2 := Model_OffsetDefinitions, child_3 := Model_DistortionConventions}

end MetricDistortion.Certified
