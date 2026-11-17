import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_RealMachine
theorem proved : Statement := by
  have halt_none (P : Program) (s : MachineState) (hs : Halted P s) : step P s = none := by
    change P[s.pc]? = some .halt at hs
    simp [step,hs]
  constructor
  · intro P k s t u hr
    induction hr generalizing u with
    | zero s => intro hu; cases hu; rfl
    | succ hs hr ih =>
      intro hu
      cases hu with
      | succ hs' hu' =>
        cases Option.some.inj (hs.symm.trans hs')
        exact ih _ hu'
  · intro P k l s t u hr
    induction hr generalizing l u with
    | zero s =>
      intro hs hu hhalt
      cases hu with
      | zero => rfl
      | succ hstep htail =>
        rw [halt_none P s hs] at hstep
        cases hstep
    | @succ k s mid t hstep htail ih =>
      intro ht hu hhalt
      cases hu with
      | zero =>
        rw [halt_none P s hhalt] at hstep
        cases hstep
      | succ hstep' htail' =>
        cases Option.some.inj (hstep.symm.trans hstep')
        exact ih _ _ ht htail' hhalt
#print axioms proved
end MetricDistortion.Contracts.Computation_RealMachine
