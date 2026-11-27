import OAI.Computability.QuantumFactoring.BitStackAdder
import OAI.Optimization.LinearProgramming.OracleSpec.ArithmeticEncoding

/-! Finite stack procedures for a raw rational field and the dyadic denominator. -/

set_option autoImplicit false

namespace EF1FPO.PricePacketProcedures

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec

def rawRatField (q : ℚ × Word) : Word := encodeRat q.1 ++ q.2

def nativeRatField : ℚ × Word → Word := prodCode ratCode id

noncomputable def decodeRatField : Procedure rawRatField nativeRatField id := by
  let tailCode : ℕ × Word → Word := prodCode Nat.bits id
  let fieldsCode : ℕ × (ℕ × Word) → Word := prodCode Nat.bits tailCode
  let fields : Procedure rawRatField fieldsCode
      (fun x => (x.1.num.natAbs, x.1.den, x.2)) :=
    (Procedure.tail.precompose rawRatField).result (by
      intro x
      simp [rawRatField, encodeRat, encodeNat, fieldsCode, tailCode, prodCode, pairBits,
        quoteBits_eq_frame, List.append_assoc])
  let sign : Procedure rawRatField boolCode (fun x => decide (x.1.num < 0)) :=
    (Procedure.head.precompose rawRatField).congrFun (by intro x; simp [rawRatField, encodeRat])
  let magnitude := (first Nat.bits tailCode).comp fields
  let suffix := (second Nat.bits tailCode).comp fields
  let denominator := (first Nat.bits (id : Word → Word)).comp suffix
  let unparsed := (second Nat.bits (id : Word → Word)).comp suffix
  let numerator := signedInt.comp (sign.pair magnitude)
  let rat := makeRat.comp (numerator.pair denominator)
  exact (rat.pair unparsed).congrFun (by
    rintro ⟨r, rest⟩
    change (mkRat (intOfSign (intData r.num)) r.den, rest) = (r, rest)
    rw [intOfSign_data, Rat.mkRat_eq_div, Rat.num_div_den])

noncomputable def powTwo : Procedure unaryCode Nat.bits (fun s : ℕ => 2 ^ s) := by
  let degree := iterateLinear double 1 double_bits_length
  let initial := (identity unaryCode).pair (constant unaryCode Nat.bits 1)
  refine (degree.comp initial).congrFun ?_
  intro s
  change (fun n : ℕ => 2 * n)^[s] 1 = 2 ^ s
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ, Nat.mul_comm]

end EF1FPO.PricePacketProcedures
