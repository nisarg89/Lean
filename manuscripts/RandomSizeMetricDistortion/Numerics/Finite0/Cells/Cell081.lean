import RandomSizeMetricDistortion.Numerics.Finite0.Tasks.Cell81_low_first_bottom
import RandomSizeMetricDistortion.Numerics.Finite0.Tasks.Cell81_low_first_top
import RandomSizeMetricDistortion.Numerics.Finite0.Tasks.Cell81_high_first_bottom
import RandomSizeMetricDistortion.Numerics.Finite0.Tasks.Cell81_high_first_top
import RandomSizeMetricDistortion.Numerics.Finite0.Tasks.Cell81_high_internal_top
set_option linter.all false
set_option maxHeartbeats 0
set_option maxRecDepth 0
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open scoped BigOperators
open Set

namespace MetricDistortion.Contracts.Numerics_Finite0Cell081
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := FiniteOneSourceBounds ⟨81, by decide⟩
theorem from_children (h : Needs) : Statement := by
  constructor
  · exact (MetricDistortion.Contracts.Numerics_Finite0Task_Cell81_low_first_bottom.from_children h)
  · exact (MetricDistortion.Contracts.Numerics_Finite0Task_Cell81_low_first_top.from_children h)
  · intro p a A r hp hpcell hL hT hk0 hk1 hr ha hap hpA hAr
    have hlo : (rootHighs.getD 0 0 : ℝ) ≤ ((sourceCell 81).lo : ℝ) := by norm_num [sourceCell,sourceCells,cell81,rootLows,rootHighs,bStar]
    have hplt : (rootHighs.getD 0 0 : ℝ) < p := hlo.trans_lt hpcell.1
    have hpr : p ≤ (rootHighs.getD 0 0 : ℝ) := hpA.trans (hAr.trans hr.2)
    linarith
  · exact (MetricDistortion.Contracts.Numerics_Finite0Task_Cell81_high_first_bottom.from_children h)
  · exact (MetricDistortion.Contracts.Numerics_Finite0Task_Cell81_high_first_top.from_children h)
  · intro p a A r hp hpcell hL hT hkb hr ha hap hpA hAr hcase
    have hlo : bStar ≤ ((sourceCell 81).lo : ℝ) := by norm_num [sourceCell,sourceCells,cell81,rootLows,rootHighs,bStar]
    have hplt : bStar < p := hlo.trans_lt hpcell.1
    linarith
  · exact (MetricDistortion.Contracts.Numerics_Finite0Task_Cell81_high_internal_top.from_children h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Cell081
