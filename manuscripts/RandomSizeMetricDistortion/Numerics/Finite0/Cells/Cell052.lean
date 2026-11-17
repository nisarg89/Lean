import RandomSizeMetricDistortion.Numerics.Finite0.Tasks.Cell52_low_first_bottom
import RandomSizeMetricDistortion.Numerics.Finite0.Tasks.Cell52_low_internal
import RandomSizeMetricDistortion.Numerics.Finite0.Tasks.Cell52_high_first_bottom
import RandomSizeMetricDistortion.Numerics.Finite0.Tasks.Cell52_high_internal_bottom
set_option linter.all false
set_option maxHeartbeats 0
set_option maxRecDepth 0
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open scoped BigOperators
open Set

namespace MetricDistortion.Contracts.Numerics_Finite0Cell052
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := FiniteOneSourceBounds ⟨52, by decide⟩
theorem from_children (h : Needs) : Statement := by
  constructor
  · exact (MetricDistortion.Contracts.Numerics_Finite0Task_Cell52_low_first_bottom.from_children h)
  · intro p a r hp hpcell hL hT hk0 hk1 hr ha hap hcase
    have hhi : ((sourceCell 52).hi : ℝ) ≤ (rootLows.getD 0 0 : ℝ) := by norm_num [sourceCell,sourceCells,cell52,rootLows,rootHighs,bStar]
    have hple : p ≤ (rootLows.getD 0 0 : ℝ) := hpcell.2.trans hhi
    have hap0 : a ≤ p := hap.trans (min_le_left _ _)
    linarith
  · exact (MetricDistortion.Contracts.Numerics_Finite0Task_Cell52_low_internal.from_children h)
  · exact (MetricDistortion.Contracts.Numerics_Finite0Task_Cell52_high_first_bottom.from_children h)
  · intro p a r hp hpcell hL hT hkb hr ha hap hcase
    have hhi : ((sourceCell 52).hi : ℝ) ≤ bStar := by norm_num [sourceCell,sourceCells,cell52,rootLows,rootHighs,bStar]
    have hple : p ≤ bStar := hpcell.2.trans hhi
    have hap0 : a ≤ p := hap.trans (min_le_left _ _)
    linarith
  · exact (MetricDistortion.Contracts.Numerics_Finite0Task_Cell52_high_internal_bottom.from_children h)
  · intro p a A r hp hpcell hL hT hkb hr ha hap hpA hAr hcase
    have hhi : ((sourceCell 52).hi : ℝ) ≤ bStar := by norm_num [sourceCell,sourceCells,cell52,rootLows,rootHighs,bStar]
    have hple : p ≤ bStar := hpcell.2.trans hhi
    linarith
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Cell052
