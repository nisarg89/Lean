import EF1FPO.BisectionDriver

/-! Charged projections from the controller's existing nested pair encoding. -/

set_option autoImplicit false

namespace EF1FPO.BisectionDriver

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure

structure ProgressAccess where
  n : Procedure encodeProgress unaryCode (fun p => p.input.n)
  b : Procedure encodeProgress unaryCode (fun p => p.input.b)
  k : Procedure encodeProgress unaryCode (fun p => p.input.k)
  index : Procedure encodeProgress unaryCode (fun p => p.index.val)
  bounds : Procedure encodeProgress boundsCode Progress.bounds

noncomputable def progressAccess : ProgressAccess := by
  let doneCode := listCode intCode
  let tailBounds := prodCode boundsCode doneCode
  let tailIndex := prodCode unaryCode tailBounds
  let tailK := prodCode unaryCode tailIndex
  let tailB := prodCode unaryCode tailK
  let tailN := prodCode unaryCode tailB
  let fields (p : Progress) :=
    (p.input.n, p.input.b, p.input.k, p.index.val, p.round, p.bounds, p.completed)
  let n := (first unaryCode tailN).precompose fields
  let afterN := (second unaryCode tailN).precompose fields
  let b := (first unaryCode tailB).comp afterN
  let afterB := (second unaryCode tailB).comp afterN
  let k := (first unaryCode tailK).comp afterB
  let afterK := (second unaryCode tailK).comp afterB
  let index := (first unaryCode tailIndex).comp afterK
  let afterIndex := (second unaryCode tailIndex).comp afterK
  let afterRound := (second unaryCode tailBounds).comp afterIndex
  let bounds := (first boundsCode doneCode).comp afterRound
  exact ⟨n, b, k, index, bounds⟩

end EF1FPO.BisectionDriver
