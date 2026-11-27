import EF1FPO.BisectionState
import EF1FPO.PricePacketProcedures
import OAI.Computability.QuantumFactoring.BitStackRationalDivision
import OAI.Computability.QuantumFactoring.BitStackUnary
import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic
import OAI.Optimization.LinearProgramming.OracleSpec.ArithmeticEncoding

/-! Closed arithmetic for the bisection controller's integer grid. -/

set_option autoImplicit false

namespace EF1FPO

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open PricePacketProcedures

abbrev boundsCode := prodCode intCode intCode

def bisectionThreshold (k : ℕ) (bounds : ℤ × ℤ) : ℚ :=
  (bisectionMidpoint bounds : ℚ) / (2 : ℚ) ^ bisectionGrid k

def bisectionOutput (k : ℕ) (coordinates : List ℤ) : Word :=
  encodeUnary (bisectionGrid k) ++ coordinates.flatMap (fun z : ℤ => encodeRat (z : ℚ))

noncomputable def bisectionInitialP : Procedure unaryCode boundsCode bisectionInitial := by
  let twice := unaryAdd.comp ((identity unaryCode).pair (identity unaryCode))
  let exponent : Procedure unaryCode unaryCode bisectionGrid :=
    (unaryAdd.comp (twice.pair (constant unaryCode unaryCode 5))).congrFun (by
      intro k
      change (k + k) + 5 = bisectionGrid k
      unfold bisectionGrid
      omega)
  let magnitude := natToInt.comp (powTwo.comp exponent)
  exact ((intNeg.comp magnitude).pair magnitude).congrFun (by
    intro k
    change (-((2 ^ bisectionGrid k : ℕ) : ℤ), ((2 ^ bisectionGrid k : ℕ) : ℤ)) =
      bisectionInitial k
    simp [bisectionInitial])

noncomputable def bisectionThresholdP :
    Procedure (prodCode unaryCode boundsCode) ratCode
      (fun z => bisectionThreshold z.1 z.2) := by
  let readK := first unaryCode boundsCode
  let twice := unaryAdd.comp ((identity unaryCode).pair (identity unaryCode))
  let exponent : Procedure unaryCode unaryCode bisectionGrid :=
    (unaryAdd.comp (twice.pair (constant unaryCode unaryCode 5))).congrFun (by
      intro k
      change (k + k) + 5 = bisectionGrid k
      unfold bisectionGrid
      omega)
  let scale := natToRat.comp (powTwo.comp (exponent.comp readK))
  let average := ratDiv.comp ((intToRat.comp intAdd).pair (constant boundsCode ratCode (2 : ℚ)))
  let midpoint : Procedure boundsCode intCode bisectionMidpoint :=
    (ratFloor.comp average).congrFun (by
      intro z
      change ⌊((z.1 + z.2 : ℤ) : ℚ) / 2⌋ = (z.1 + z.2) / 2
      simpa using Rat.floor_intCast_div_natCast (z.1 + z.2) 2)
  let numerator := intToRat.comp (midpoint.comp (second unaryCode boundsCode))
  exact (ratDiv.comp (numerator.pair scale)).congrFun (by
    intro z
    change (bisectionMidpoint z.2 : ℚ) / ((2 ^ bisectionGrid z.1 : ℕ) : ℚ) =
      bisectionThreshold z.1 z.2
    simp [bisectionThreshold])

noncomputable def bisectionNextP :
    Procedure (fun p : Bool × (ℕ × (ℤ × ℤ)) => p.1 :: prodCode unaryCode boundsCode p.2)
      boundsCode (fun z => bisectionNext z.2.1 z.2.2 z.1) := by
  let inputCode := prodCode unaryCode boundsCode
  let k := first unaryCode boundsCode
  let bounds := second unaryCode boundsCode
  let lo := (first intCode intCode).comp bounds
  let hi := (second intCode intCode).comp bounds
  let average := ratDiv.comp ((intToRat.comp intAdd).pair (constant boundsCode ratCode (2 : ℚ)))
  let midpoint : Procedure boundsCode intCode bisectionMidpoint :=
    (ratFloor.comp average).congrFun (by
      intro z
      change ⌊((z.1 + z.2 : ℤ) : ℚ) / 2⌋ = (z.1 + z.2) / 2
      simpa using Rat.floor_intCast_div_natCast (z.1 + z.2) 2)
  let mid := midpoint.comp bounds
  let exponent := unaryAdd.comp (k.pair (constant inputCode unaryCode 3))
  let margin : Procedure inputCode intCode (fun z => bisectionMargin z.1) :=
    (natToInt.comp (powTwo.comp exponent)).congrFun (by
      intro z
      change ((2 ^ (z.1 + 3) : ℕ) : ℤ) = bisectionMargin z.1
      simp [bisectionMargin])
  let upper := intAdd.comp (mid.pair margin)
  let lower := intSub.comp (mid.pair margin)
  let capHi : Procedure inputCode intCode
      (fun z => min z.2.2 (bisectionMidpoint z.2 + bisectionMargin z.1)) :=
    (conditional (Arithmetic.intLe.comp (hi.pair upper)) hi upper).congrFun (by
      intro z
      simp [Function.comp_apply, min_def])
  let capLo : Procedure inputCode intCode
      (fun z => max z.2.1 (bisectionMidpoint z.2 - bisectionMargin z.1)) :=
    (conditional (Arithmetic.intLe.comp (lo.pair lower)) lower lo).congrFun (by
      intro z
      simp [Function.comp_apply, max_def])
  exact (chooseBit (lo.pair capHi) (capLo.pair hi)).congrFun (by
    rintro ⟨sign, k, lo, hi⟩
    cases sign <;> rfl)

noncomputable def bisectionOutputP :
    Procedure (prodCode unaryCode (listCode intCode)) id
      (fun z => bisectionOutput z.1 z.2) := by
  let inputCode := prodCode unaryCode (listCode intCode)
  let k := first unaryCode (listCode intCode)
  let coordinates := second unaryCode (listCode intCode)
  let twice := unaryAdd.comp (k.pair k)
  let exponent : Procedure inputCode unaryCode (fun p => bisectionGrid p.1) :=
    (unaryAdd.comp (twice.pair (constant inputCode unaryCode 5))).congrFun (by
      intro z
      change (z.1 + z.1) + 5 = bisectionGrid z.1
      unfold bisectionGrid
      omega)
  let prefixBits : Procedure inputCode id (fun z => unaryCode (bisectionGrid z.1)) :=
    exponent.result (fun _ => rfl)
  let header := Procedure.append.comp (prefixBits.pair (constant inputCode id [false]))
  let writeInt := Wire.writeRat.comp intToRat
  let bits := (Wire.flatten.comp (Procedure.listMap (0 : ℤ) ([] : Word) writeInt)).comp coordinates
  exact (Procedure.append.comp (header.pair bits)).congrFun (by intro z; rfl)

end EF1FPO
