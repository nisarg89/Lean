import EF1FPO.HeaderProcedures
import EF1FPO.PricePackets
import EF1FPO.ProcedureTime
import EF1FPO.VectorProcedures
import OAI.Computability.QuantumFactoring.BitStackRationalDivision

/-! Finite-stack evaluation of the designated anchored-price comparison. -/

set_option autoImplicit false

namespace EF1FPO

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open PricePacketProcedures

noncomputable def anchoredAnswerProcedure :
    Procedure AnchoredPriceAnswer.encode id (fun a => [a.compare]) := by
  let values (a : AnchoredPriceAnswer) : List ℚ :=
    List.ofFn (fun i => (a.numerator i : ℚ))
  let array (a : AnchoredPriceAnswer) := rawRatList (values a)
  let afterIndex (a : AnchoredPriceAnswer) := rawRatField (a.rawCoordinate, array a)
  let afterPrecision (a : AnchoredPriceAnswer) := rawNatField (a.designated.val, afterIndex a)
  let afterDimension (a : AnchoredPriceAnswer) := rawUnaryField (a.precision, afterPrecision a)
  let readN : Procedure AnchoredPriceAnswer.encode (prodCode unaryCode id)
      (fun a => (a.n, afterDimension a)) :=
    (decodeUnaryField.precompose (fun a : AnchoredPriceAnswer => (a.n, afterDimension a))).congrEncoding
      (by intro a
          simp [rawUnaryField, rawNatField, rawRatField, rawRatList, values, array,
            afterDimension, afterPrecision, afterIndex, AnchoredPriceAnswer.encode,
            encodeUnary, encodeGrid, List.append_assoc])
      (by intro x; rfl)
  let readPrecision := readSuffix ((second unaryCode id).comp readN)
    (decodeUnaryField.precompose (fun a : AnchoredPriceAnswer => (a.precision, afterPrecision a)))
  let readIndex := readSuffix ((second unaryCode id).comp readPrecision)
    (decodeNatField.precompose (fun a : AnchoredPriceAnswer => (a.designated.val, afterIndex a)))
  let readRaw := readSuffix ((second Nat.bits id).comp readIndex)
    (decodeRatField.precompose (fun a : AnchoredPriceAnswer => (a.rawCoordinate, array a)))
  let dimension := (first unaryCode id).comp readN
  let scale := (first unaryCode id).comp readPrecision
  let index := (first Nat.bits id).comp readIndex
  let raw := (first ratCode id).comp readRaw
  let remaining := (second ratCode id).comp readRaw
  let packed : Procedure AnchoredPriceAnswer.encode countedRatList values :=
    (dimension.pair remaining).result (by
      intro a
      change prodCode unaryCode id (a.n, array a) = countedRatList (values a)
      simp [array, countedRatList, values])
  let decoded := decodeRatList.comp packed
  let numerator := (Procedure.listGet (ea := ratCode) (0 : ℚ)).comp (index.pair decoded)
  let denominator := natToRat.comp (powTwo.comp scale)
  let scaled := ratDiv.comp (numerator.pair denominator)
  let compare := Arithmetic.ratLe.comp (raw.pair scaled)
  exact compare.result (by
    intro a
    have valueAt : ((values a).drop a.designated.val).headD 0 = (a.numerator a.designated : ℚ) := by
      simp [values, a.designated.isLt]
    change [decide (a.rawCoordinate ≤ ((values a).drop a.designated.val).headD 0 /
      ((2 ^ a.precision : ℕ) : ℚ))] = [a.compare]
    rw [valueAt]
    simp [AnchoredPriceAnswer.compare, div_eq_mul_inv])

theorem AnchoredPriceAnswer.binary :
    BitPolynomial AnchoredPriceAnswer.encode (fun a output => output = [a.compare]) :=
  bitPolynomial_of_procedure anchoredAnswerProcedure

end EF1FPO
