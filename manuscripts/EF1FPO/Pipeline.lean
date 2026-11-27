import EF1FPO.PreparedRelay
import EF1FPO.GraphStage

/-! Composition of the physical preparation, graph, weight, rounding and return stages. -/

set_option autoImplicit false

namespace EF1FPO.Pipeline

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec

structure Program where
  output : Instance → Word
  procedure : Procedure encodeInstance id output
  correct : ∀ I : Instance, ∃ A : I.Allocation,
    I.IsEF1 A ∧ I.IsFPO A ∧ output I = encodeAllocation A

noncomputable def composed : Program := by
  let selected := PreparedRelay.selected
  let prepared : Procedure encodeInstance id (fun I => encodeInstance (selected I).inst) :=
    PreparedRelay.preparedInstance.comp PreparedRelay.prepare
  let forGraph : Procedure encodeInstance (fun d : PreparedInput => encodeInstance d.inst) selected :=
    prepared.result (by intro I; rfl)
  let masks := GreatestGraphStage.procedure.comp forGraph
  let graphInput (I : Instance) : GreatestGraphInput :=
    let h := GreatestGraphStage.output_correct (selected I)
    ⟨selected I, Classical.choose h, (Classical.choose_spec h).1⟩
  let feedWeight : Procedure encodeInstance GreatestGraphInput.encode graphInput :=
    (Procedure.append.comp (prepared.pair masks)).result (by
      intro I
      change encodeInstance (selected I).inst ++ GreatestGraphStage.output (selected I) = _
      exact congrArg (fun word => encodeInstance (selected I).inst ++ word)
        (Classical.choose_spec (GreatestGraphStage.output_correct (selected I))).2)
  let weights := GreatestWeightStage.procedure.comp feedWeight
  let roundInput (I : Instance) : RoundingInput :=
    let h := GreatestWeightStage.output_correct (graphInput I)
    ⟨selected I, Classical.choose h, (Classical.choose_spec h).1⟩
  let feedRound : Procedure encodeInstance RoundingInput.encode roundInput :=
    (Procedure.append.comp (prepared.pair weights)).result (by
      intro I
      change encodeInstance (selected I).inst ++ GreatestWeightStage.output (graphInput I) = _
      exact congrArg (fun word => encodeInstance (selected I).inst ++ word)
        (Classical.choose_spec (GreatestWeightStage.output_correct (graphInput I))).2)
  let allocations := RoundStage.procedure.comp feedRound
  let recoveryInput (I : Instance) : RecoveryInput :=
    let d := roundInput I
    let h := RoundStage.output_correct d
    let A := Classical.choose h
    let hA := Classical.choose_spec h
    let w := fun i : d.prepared.inst.Agent => (d.weights i : ℝ)
    let hw : d.prepared.inst.Positive w := d.greatest.1.1
    ⟨d.prepared, A, d.prepared.inst.ef1_of_bands w A 1 hw hA.1 hA.2.1, ⟨w, hw, hA.1⟩⟩
  let rawPreparation : Procedure encodeInstance id
      (fun I => PreparedRelay.preparationCode (selected I)) :=
    PreparedRelay.prepare.result (by intro I; rfl)
  let original : Procedure encodeInstance id encodeInstance :=
    (identity encodeInstance).result (by intro I; rfl)
  let context := Procedure.append.comp (original.pair rawPreparation)
  let feedRecovery : Procedure encodeInstance RecoveryInput.encode recoveryInput :=
    (Procedure.append.comp (context.pair allocations)).result (by
      intro I
      change (encodeInstance I ++ PreparedRelay.preparationCode (selected I)) ++
        RoundStage.output (roundInput I) = _
      exact congrArg (fun word => (encodeInstance I ++ PreparedRelay.preparationCode (selected I)) ++ word)
        (Classical.choose_spec (RoundStage.output_correct (roundInput I))).2.2)
  let finish := ReturnStage.procedure.comp feedRecovery
  refine ⟨fun I => ReturnStage.output (recoveryInput I), finish, ?_⟩
  intro I
  obtain ⟨A, _, hEF1, ⟨q, hPositive, hSupport⟩, hEq⟩ :=
    ReturnStage.output_correct (recoveryInput I)
  exact ⟨A, hEF1, I.fpo_of_supported (fun i => (q i : ℝ)) A hPositive hSupport, hEq⟩

end EF1FPO.Pipeline
