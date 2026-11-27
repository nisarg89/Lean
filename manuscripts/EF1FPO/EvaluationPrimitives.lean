import EF1FPO.EvaluationMath
import EF1FPO.HeaderProcedures
import OAI.Optimization.LinearProgramming.PriceGame.ControlRatListSum
import OAI.Optimization.LinearProgramming.PriceGame.ControlScalarMachine

/-! Guarded logarithms, seeded rational extrema and rounding on native scalar wires. -/

set_option autoImplicit false

namespace EF1FPO.EvaluationWire

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec

def logPairCode : ℚ × ℕ → Word := prodCode ratCode unaryCode

noncomputable def guardedLogProcedure :
    Procedure logPairCode ratCode (fun x => guardedLog x.1 x.2) := by
  let q := first ratCode unaryCode
  let t := second ratCode unaryCode
  let zero := constant logPairCode ratCode (0 : ℚ)
  let one := constant logPairCode ratCode (1 : ℚ)
  let positive := conditional (Arithmetic.ratLt.comp (zero.pair q)) q one
  let qWord := Wire.writeRat.comp positive
  let tRaw : Procedure logPairCode id (fun x => unaryCode x.2) := t.result (fun _ => rfl)
  let tWord := Procedure.append.comp (tRaw.pair (constant logPairCode id [false]))
  let joined := Procedure.append.comp (qWord.pair tWord)
  let inputP : Procedure logPairCode encodeLogInput (fun x => guardedLogInput x.1 x.2) :=
    joined.result (by
      intro x
      simp [guardedLogInput, encodeLogInput, encodeUnary, unaryCode, Function.comp_apply])
  let outputP := evaluateLogProcedure.comp inputP
  let readP := PricePacketProcedures.decodeRatField.precompose
    (fun x : ℚ × ℕ => (guardedLog x.1 x.2, []))
  let suffixP := PricePacketProcedures.readSuffix outputP
    (readP.congrEncoding (by intro x; simp [PricePacketProcedures.rawRatField, guardedLog, Function.comp_apply])
      (fun _ => rfl))
  exact ((first ratCode id).comp suffixP).congrFun (fun _ => rfl)

def maximum (xs : List ℚ × ℚ) : ℚ := xs.1.foldl (fun a q => max q a) xs.2

def minimum (xs : List ℚ × ℚ) : ℚ := xs.1.foldl (fun a q => min q a) xs.2

noncomputable def maximumProcedure :
    Procedure (prodCode (listCode ratCode) ratCode) ratCode maximum := by
  apply foldList (0 : ℚ) OAI.Optimization.LinearProgramming.PriceGame.Control.Native.ratMaxP Polynomial.X
  intro xs a i
  rw [Polynomial.eval_X]
  have selects (ys : List ℚ) (b : ℚ) :
      let value := ys.foldl (fun best q => max q best) b
      value = b ∨ value ∈ ys := by
    induction ys generalizing b with
    | nil => exact Or.inl rfl
    | cons y ys ih =>
      simp only [List.foldl_cons]
      rcases ih (max y b) with h | h
      · rcases max_choice y b with h' | h'
        · exact Or.inr (List.mem_cons.mpr (Or.inl (h.trans h')))
        · exact Or.inl (h.trans h')
      · exact Or.inr (List.mem_cons_of_mem _ h)
  rcases selects (xs.take i) a with same | member
  · change (ratCode ((xs.take i).foldl (fun best q => max q best) a)).length ≤ _
    rw [same]
    omega
  · have size := code_le_of_mem ratCode (List.mem_of_mem_take member)
    exact size.trans (Nat.le_add_right _ _)

noncomputable def minimumProcedure :
    Procedure (prodCode (listCode ratCode) ratCode) ratCode minimum := by
  apply foldList (0 : ℚ) OAI.Optimization.LinearProgramming.PriceGame.Control.Native.ratMinP Polynomial.X
  intro xs a i
  rw [Polynomial.eval_X]
  have selects (ys : List ℚ) (b : ℚ) :
      let value := ys.foldl (fun best q => min q best) b
      value = b ∨ value ∈ ys := by
    induction ys generalizing b with
    | nil => exact Or.inl rfl
    | cons y ys ih =>
      simp only [List.foldl_cons]
      rcases ih (min y b) with h | h
      · rcases min_choice y b with h' | h'
        · exact Or.inr (List.mem_cons.mpr (Or.inl (h.trans h')))
        · exact Or.inl (h.trans h')
      · exact Or.inr (List.mem_cons_of_mem _ h)
  rcases selects (xs.take i) a with same | member
  · change (ratCode ((xs.take i).foldl (fun best q => min q best) a)).length ≤ _
    rw [same]
    omega
  · have size := code_le_of_mem ratCode (List.mem_of_mem_take member)
    exact size.trans (Nat.le_add_right _ _)

noncomputable def roundedNumeratorProcedure :
    Procedure (prodCode unaryCode ratCode) intCode (fun x => roundedNumerator x.1 x.2) := by
  let code := prodCode unaryCode ratCode
  let power := natToRat.comp (PricePacketProcedures.powTwo.comp (first unaryCode ratCode))
  let q := second unaryCode ratCode
  let hi := OAI.Optimization.LinearProgramming.PriceGame.Control.Native.ratMinP.comp
    ((constant code ratCode (1 : ℚ)).pair q)
  let clip := OAI.Optimization.LinearProgramming.PriceGame.Control.Native.ratMaxP.comp
    ((constant code ratCode (-1 : ℚ)).pair hi)
  let scaled := ratMul.comp (power.pair clip)
  let shifted := ratAdd.comp (scaled.pair (constant code ratCode (1 / 2 : ℚ)))
  exact (ratFloor.comp shifted).congrFun (by
    intro x
    simp [Function.comp_apply, roundedNumerator, Nat.cast_pow])

end EF1FPO.EvaluationWire
