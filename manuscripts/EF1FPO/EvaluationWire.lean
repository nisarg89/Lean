import EF1FPO.Algorithm
import EF1FPO.VectorProcedures
import EF1FPO.HeaderProcedures
import OAI.Computability.QuantumFactoring.BitStackUnary
import OAI.Optimization.LinearProgramming.OracleSpec.GuardedIteration

/-! Parse retained valuations and dyadic coordinates through the existing binary wires. -/

set_option autoImplicit false

namespace EF1FPO.EvaluationWire

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open PricePacketProcedures

abbrev Table := ℕ × (ℕ × (ℕ × List (List ℚ)))

def tableCode : Table → Word :=
  prodCode unaryCode (prodCode unaryCode (prodCode unaryCode (listCode (listCode ratCode))))

def table (I : Instance) : Table :=
  (I.n, I.m, valuationBits I, List.ofFn (fun i : I.Agent => List.ofFn (I.v i)))

def framedInstance (w : Instance × Word) : Word := frame (encodeInstance w.1) ++ w.2

def tableSuffixCode : Table × Word → Word := prodCode tableCode id

def decodeTable (w : Instance × Word) : Table × Word := (table w.1, w.2)

noncomputable def readFrameProcedure : Procedure framedInstance tableSuffixCode decodeTable := by
  let split : Procedure framedInstance (prodCode encodeInstance id) id :=
    (identity (prodCode encodeInstance id)).congrEncoding
      (by intro p; simp only [framedInstance, prodCode, pairBits, id_eq, quoteBits_eq_frame])
      (fun _ => rfl)
  let instanceP := (first encodeInstance id).comp split
  let suffixP := (second encodeInstance id).comp split
  let nativeP : Procedure encodeInstance InstanceWire.decodedInstanceCode
      (fun I => InstanceWire.decodeInstance (I, [])) :=
    (InstanceWire.decodeInstancePrefix.precompose (fun I : Instance => (I, []))).congrEncoding
      (by intro I; simp) (fun _ => rfl)
  let decoded := nativeP.comp instanceP
  let rationalData := prodCode (listCode ratCode) id
  let mAndData := prodCode unaryCode rationalData
  let n := (first unaryCode mAndData).comp decoded
  let mData := (second unaryCode mAndData).comp decoded
  let m := (first unaryCode rationalData).comp mData
  let cells := (first (listCode ratCode) id).comp ((second unaryCode rationalData).comp mData)
  let data := PreparationMatrixWire.unpackRowsProcedure.comp (n.pair (m.pair cells))
  let length := (Fuel.lengthInUnary encodeInstance).comp instanceP
  let four := constant framedInstance unaryCode 4
  let bits := conditional (unaryLe.comp (four.pair length)) length four
  exact ((n.pair (m.pair (bits.pair data))).pair suffixP).congrFun (by
    intro p
    simp only [Function.comp_apply, Prod.fst, Prod.snd, id_eq, InstanceWire.decodeInstance,
      PreparationMatrixWire.unpackRows_agrees, decodeTable, table]
    rw [valuationBits, max_eq_right (dimensions_le_binarySize p.1), max_def]
    simp only [decide_eq_true_eq])

abbrev EvaluationData := Table × (ℕ × (ℕ × List ℚ))

def dataCode : EvaluationData → Word :=
  prodCode tableCode (prodCode unaryCode (prodCode unaryCode (listCode ratCode)))

def decodeEvaluation (d : EvaluationInput) : EvaluationData :=
  (table d.prepared.inst, d.inputPrecision, d.precision, List.ofFn (fun i => (d.numerator i : ℚ)))

noncomputable def decodeEvaluationProcedure :
    Procedure EvaluationInput.encode dataCode decodeEvaluation := by
  let nums (d : EvaluationInput) : List ℚ := List.ofFn (fun i => (d.numerator i : ℚ))
  let remaining (d : EvaluationInput) := rawUnaryField (d.precision, encodeGrid d.numerator)
  let allFields (d : EvaluationInput) := rawUnaryField (d.inputPrecision, remaining d)
  let tables : Procedure EvaluationInput.encode tableSuffixCode
      (fun d => (table d.prepared.inst, allFields d)) :=
    (readFrameProcedure.precompose (fun d : EvaluationInput => (d.prepared.inst, allFields d))).congrEncoding
      (by intro d
          simp [EvaluationInput.encode, framedInstance, allFields, remaining, rawUnaryField,
            dyadicQuery, encodeUnary, List.append_assoc])
      (fun _ => rfl)
  let header := (first tableCode id).comp tables
  let rest := (second tableCode id).comp tables
  let beforeInput := readSuffix rest
    (decodeUnaryField.precompose (fun d : EvaluationInput => (d.inputPrecision, remaining d)))
  let beforeOutput := readSuffix ((second unaryCode id).comp beforeInput)
    (decodeUnaryField.precompose (fun d : EvaluationInput => (d.precision, encodeGrid d.numerator)))
  let source := (first unaryCode id).comp beforeInput
  let target := (first unaryCode id).comp beforeOutput
  let grid := (second unaryCode id).comp beforeOutput
  let n := (first unaryCode (prodCode unaryCode (prodCode unaryCode (listCode (listCode ratCode))))).comp header
  let countGrid : Procedure EvaluationInput.encode countedRatList nums :=
    (n.pair grid).result (by intro d; simp [nums, table, encodeGrid, countedRatList, rawRatList])
  let decoded := decodeRatList.comp countGrid
  exact (header.pair (source.pair (target.pair decoded))).congrFun (fun _ => rfl)

end EF1FPO.EvaluationWire
