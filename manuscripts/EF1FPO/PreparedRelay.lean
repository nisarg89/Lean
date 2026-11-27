import EF1FPO.Algorithm

/-! Recover the canonical instance prefix while keeping the preparation packet available. -/

set_option autoImplicit false

namespace EF1FPO.PreparedRelay

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.Optimization.LinearProgramming.PriceGame
open EF1FPO.InstanceWire

noncomputable def selected (I : Instance) : PreparedInput :=
  let witness := PrepareStage.output_correct I
  ⟨I, Classical.choose witness, (Classical.choose_spec witness).1⟩

def preparationCode (d : PreparedInput) : Word := encodePreparation d.preparation

noncomputable def prepare : Procedure encodeInstance preparationCode selected :=
  PrepareStage.procedure.result (by
    intro I
    exact (Classical.choose_spec (PrepareStage.output_correct I)).2)

noncomputable def preparedInstance : Procedure preparationCode id (fun d => encodeInstance d.inst) := by
  let suffix (d : PreparedInput) :=
    encodeNat d.preparation.keptCount ++
      (List.ofFn (fun g => (d.preparation.keptGood g).val)).flatMap encodeNat
  let fields (d : PreparedInput) : Instance × Word := (d.inst, suffix d)
  let base : Procedure preparationCode decodedInstanceCode (fun d => decodeInstance (fields d)) :=
    (decodeInstancePrefix.precompose fields).congrEncoding
      (by intro d; simp [fields, preparationCode, encodePreparation, PreparedInput.inst, suffix, List.append_assoc])
      (by intro d; rfl)
  let values := prodCode (listCode ratCode) id
  let body := prodCode unaryCode values
  let n := (first unaryCode body).comp base
  let tail := (second unaryCode body).comp base
  let m := (first unaryCode values).comp tail
  let entries := (first (listCode ratCode) id).comp ((second unaryCode values).comp tail)
  let writeNat := Wire.writeNat.comp unaryToBits
  let writeLabels := (Wire.flatten.comp (Procedure.listMap (0 : ℕ) ([] : Word) Wire.writeNat)).comp
    Control.Native.addressRangeP
  let rowHeader := writeNat.comp n
  let colHeader := writeNat.comp m
  let rowLabels := writeLabels.comp n
  let colLabels := writeLabels.comp m
  let valueWords := (Wire.flatten.comp (Procedure.listMap (0 : ℚ) ([] : Word) Wire.writeRat)).comp entries
  let headers := Procedure.append.comp (rowHeader.pair colHeader)
  let labels := Procedure.append.comp (rowLabels.pair colLabels)
  let result := Procedure.append.comp (headers.pair (Procedure.append.comp (labels.pair valueWords)))
  have flatten_map {α : Type} (xs : List α) (f : α → Word) : (xs.map f).flatten = xs.flatMap f := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, ih]
  have labels_match (k : ℕ) : List.range k = List.ofFn (fun i : Fin k => i.val) := by
    apply List.ext_getElem
    · simp
    · intro j hj hj'
      simp only [List.getElem_range, List.getElem_ofFn]
  exact result.congrFun (by
    intro d
    simp only [Function.comp_apply, Prod.fst, Prod.snd, id_eq, decodeInstance, fields,
      encodeInstance, flatten_map, labels_match, List.append_assoc])

end EF1FPO.PreparedRelay
