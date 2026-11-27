import EF1FPO.EvaluationWire
import EF1FPO.EvaluationPrimitives
import OAI.Optimization.LinearProgramming.PriceGame.MarketContextMap

/-! Share decoded precision, bias height and scaled rational coordinates across stages. -/

set_option autoImplicit false

namespace EF1FPO.EvaluationWire

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec

abbrev TableTail := ℕ × (ℕ × List (List ℚ))
abbrev MatrixTail := ℕ × List (List ℚ)
def matrixTailCode : MatrixTail → Word := prodCode unaryCode (listCode (listCode ratCode))
def tableTailCode : TableTail → Word := prodCode unaryCode matrixTailCode

def tableHeight (t : Table) : ℕ := 16 * (t.1 + t.2.1 + 1) * (t.2.2.1 + 1)
def tableRadius (t : Table) : ℚ := 4 * ((t.2.2.1 : ℚ) + 1)

noncomputable def tableHeightProcedure : Procedure tableCode unaryCode tableHeight := by
  let n := first unaryCode tableTailCode
  let rest := second unaryCode tableTailCode
  let m := (first unaryCode matrixTailCode).comp rest
  let L := (first unaryCode (listCode (listCode ratCode))).comp ((second unaryCode matrixTailCode).comp rest)
  let dimensions := unarySuccessor.comp (unaryAdd.comp (n.pair m))
  let leading := unaryMul.comp ((constant tableCode unaryCode 16).pair dimensions)
  exact (unaryMul.comp (leading.pair (unarySuccessor.comp L))).congrFun (fun _ => rfl)

noncomputable def tableRadiusProcedure : Procedure tableCode ratCode tableRadius := by
  let rest := second unaryCode tableTailCode
  let L := (first unaryCode (listCode (listCode ratCode))).comp ((second unaryCode matrixTailCode).comp rest)
  let step := natToRat.comp (unaryToBits.comp (unarySuccessor.comp L))
  exact (ratMul.comp ((constant tableCode ratCode (4 : ℚ)).pair step)).congrFun (by
    intro t
    simp [Function.comp_apply, Nat.cast_add, tableRadius])

abbrev ScaleList := ℕ × (ℚ × List ℚ)

def scaleListCode : ScaleList → Word := prodCode unaryCode (prodCode ratCode (listCode ratCode))

def scaleList (x : ScaleList) := x.2.2.map (fun q => x.2.1 * (q / (2 : ℚ) ^ x.1))

noncomputable def scaleListProcedure : Procedure scaleListCode (listCode ratCode) scaleList := by
  let valuesCode := listCode ratCode
  let tailCode := prodCode ratCode valuesCode
  let source := first unaryCode tailCode
  let tail := second unaryCode tailCode
  let radius := (first ratCode valuesCode).comp tail
  let values := (second ratCode valuesCode).comp tail
  let scale := natToRat.comp (PricePacketProcedures.powTwo.comp source)
  let context := prodCode ratCode ratCode
  let readContext := first context ratCode
  let r := (first ratCode ratCode).comp readContext
  let pow := (second ratCode ratCode).comp readContext
  let coordinate := second context ratCode
  let point := ratMul.comp (r.pair (ratDiv.comp (coordinate.pair pow)))
  let mapped := OAI.Optimization.LinearProgramming.PriceGame.Market.GridMachine.mapWithContext
    (0 : ℚ) (0 : ℚ) point
  exact (mapped.comp (values.pair (radius.pair scale))).congrFun (by
    intro d
    simp [Function.comp_apply, Nat.cast_pow, scaleList])

end EF1FPO.EvaluationWire
