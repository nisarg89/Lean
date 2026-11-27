import EF1FPO.HeaderProcedures
import EF1FPO.PricePackets
import EF1FPO.ProcedureTime
import EF1FPO.VectorProcedures
import OAI.Computability.QuantumFactoring.BitStackRationalDivision
import OAI.Optimization.LinearProgramming.PriceGame.ControlScalarMachine

/-! Construct one complete dyadic oracle request and retain the designated raw coordinate. -/

set_option autoImplicit false

namespace EF1FPO

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.Optimization.LinearProgramming.PriceGame.Control.Native (ratMinP ratMaxP)
open PricePacketProcedures

noncomputable def anchoredRequestProcedure :
    Procedure AnchoredPriceRequest.encode id AnchoredPriceRequest.encodeResult := by
  let values (q : AnchoredPriceRequest) : List ℚ := List.ofFn q.prices
  let array (q : AnchoredPriceRequest) := rawRatList (values q)
  let afterThreshold (q : AnchoredPriceRequest) := rawNatField (q.designated.val, array q)
  let afterAnchor (q : AnchoredPriceRequest) := rawRatField (q.threshold, afterThreshold q)
  let afterPrecision (q : AnchoredPriceRequest) := rawNatField (q.anchor.val, afterAnchor q)
  let afterDimension (q : AnchoredPriceRequest) := rawUnaryField (q.precision, afterPrecision q)
  let readN : Procedure AnchoredPriceRequest.encode (prodCode unaryCode id)
      (fun q => (q.n, afterDimension q)) :=
    (decodeUnaryField.precompose (fun q : AnchoredPriceRequest => (q.n, afterDimension q))).congrEncoding
      (by intro q
          simp [rawUnaryField, rawNatField, rawRatField, rawRatList, values, array,
            afterDimension, afterPrecision, afterAnchor, afterThreshold, AnchoredPriceRequest.encode,
            encodeUnary, priceQuery, List.append_assoc])
      (by intro x; rfl)
  let readPrecision := readSuffix ((second unaryCode id).comp readN)
    (decodeUnaryField.precompose (fun q : AnchoredPriceRequest => (q.precision, afterPrecision q)))
  let readAnchor := readSuffix ((second unaryCode id).comp readPrecision)
    (decodeNatField.precompose (fun q : AnchoredPriceRequest => (q.anchor.val, afterAnchor q)))
  let readThreshold := readSuffix ((second Nat.bits id).comp readAnchor)
    (decodeRatField.precompose (fun q : AnchoredPriceRequest => (q.threshold, afterThreshold q)))
  let readDesignated := readSuffix ((second ratCode id).comp readThreshold)
    (decodeNatField.precompose (fun q : AnchoredPriceRequest => (q.designated.val, array q)))
  let dimension := (first unaryCode id).comp readN
  let scale := (first unaryCode id).comp readPrecision
  let anchor := (first Nat.bits id).comp readAnchor
  let threshold := (first ratCode id).comp readThreshold
  let designated := (first Nat.bits id).comp readDesignated
  let remaining := (second Nat.bits id).comp readDesignated
  let packed : Procedure AnchoredPriceRequest.encode countedRatList values :=
    (dimension.pair remaining).result (by
      intro q
      change prodCode unaryCode id (q.n, array q) = countedRatList (values q)
      simp [array, countedRatList, values])
  let decoded := decodeRatList.comp packed
  let readEntry := Procedure.listGet (ea := ratCode) (0 : ℚ)
  let toRationalDenominator := natToRat.comp (powTwo.comp scale)
  let anchorPrice := readEntry.comp (anchor.pair decoded)
  let context (q : AnchoredPriceRequest) : ℚ × (ℚ × (ℚ × List ℚ)) :=
    (q.threshold, ((2 ^ q.precision : ℕ) : ℚ), ((values q).drop q.anchor.val).headD 0, values q)
  let pricesCode := listCode ratCode
  let anchorAndPricesCode := prodCode ratCode pricesCode
  let scaleAndPricesCode := prodCode ratCode anchorAndPricesCode
  let contextCode := prodCode ratCode scaleAndPricesCode
  let readContext : Procedure AnchoredPriceRequest.encode contextCode context :=
    threshold.pair (toRationalDenominator.pair (anchorPrice.pair decoded))
  let readWire := prodCode Nat.bits contextCode
  let ctx := second Nat.bits contextCode
  let t := (first ratCode scaleAndPricesCode).comp ctx
  let scaleAndPrices := (second ratCode scaleAndPricesCode).comp ctx
  let denom := (first ratCode anchorAndPricesCode).comp scaleAndPrices
  let anchorAndPrices := (second ratCode anchorAndPricesCode).comp scaleAndPrices
  let anchorVal := (first ratCode pricesCode).comp anchorAndPrices
  let priceValues := (second ratCode pricesCode).comp anchorAndPrices
  let rawPoint (c : ℚ × (ℚ × (ℚ × List ℚ))) (i : ℕ) : ℚ :=
    c.1 + (((c.2.2.2.drop i).headD 0) - c.2.2.1) / c.2.1
  let rawProc : Procedure readWire ratCode (fun d => rawPoint d.2 d.1) :=
    ratAdd.comp (t.pair (ratDiv.comp
      ((ratSub.comp ((readEntry.comp ((first Nat.bits contextCode).pair priceValues)).pair anchorVal)).pair denom)))
  let gridInput := prodCode unaryCode contextCode
  let unaryIndex := first unaryCode contextCode
  let itemContext := second unaryCode contextCode
  let cellInput := (unaryToBits.comp unaryIndex).pair itemContext
  let rawCell := rawProc.comp cellInput
  let denomCell := denom.comp cellInput
  let clipped := ratMaxP.comp ((constant gridInput ratCode (-1 : ℚ)).pair
    (ratMinP.comp ((constant gridInput ratCode (1 : ℚ)).pair rawCell)))
  let gridPoint (c : ℚ × (ℚ × (ℚ × List ℚ))) (i : ℕ) : ℤ :=
    ⌊max (-1) (min 1 (rawPoint c i)) * c.2.1⌋
  let gridCell : Procedure gridInput intCode (fun d => gridPoint d.2 d.1) :=
    ratFloor.comp (ratMul.comp (clipped.pair denomCell))
  let produceGrid := (Procedure.tabulate (ea := contextCode) (0 : ℤ) gridCell).comp
    (dimension.pair readContext)
  let writeInt := Wire.writeRat.comp intToRat
  let serialized := Wire.flatten.comp ((Procedure.listMap (0 : ℤ) ([] : Word) writeInt).comp produceGrid)
  let precisionBits : Procedure AnchoredPriceRequest.encode id (fun q => unaryCode q.precision) :=
    scale.result (by intro q; rfl)
  let precisionWord := Procedure.append.comp
    (precisionBits.pair (constant AnchoredPriceRequest.encode id [false]))
  let packet := Procedure.append.comp (precisionWord.pair
    (Procedure.append.comp (precisionWord.pair serialized)))
  let evaluationPacket (q : AnchoredPriceRequest) : Word :=
    encodeUnary q.precision ++ (encodeUnary q.precision ++
      (List.map (encodeRat ∘ (fun z : ℤ => (z : ℚ)))
        (List.map (gridPoint (context q)) (List.range q.n))).flatten)
  let exactPacket : Procedure AnchoredPriceRequest.encode id evaluationPacket :=
    packet.congrFun (by intro q; rfl)
  let framed : Procedure AnchoredPriceRequest.encode id (fun q => frame (evaluationPacket q)) :=
    ((Procedure.quote id).comp exactPacket).result (by intro q; exact quoteBits_eq_frame _)
  let designatedRaw := Wire.writeRat.comp (rawProc.comp (designated.pair readContext))
  exact (Procedure.append.comp (framed.pair designatedRaw)).congrFun (by
    intro q
    have hAt (i : Fin q.n) : ((values q).drop i.val).headD 0 = q.prices i := by
      simp [values, i.isLt]
    have hRaw (i : Fin q.n) : rawPoint (context q) i.val = q.raw i := by
      change q.threshold + (((values q).drop i.val).headD 0 - ((values q).drop q.anchor.val).headD 0) /
        ((2 ^ q.precision : ℕ) : ℚ) = q.raw i
      rw [hAt i, hAt q.anchor]
      simp [AnchoredPriceRequest.raw, div_eq_mul_inv, mul_comm]
    have hGrid : (List.range q.n).map (gridPoint (context q)) = List.ofFn q.grid := by
      apply List.ext_getElem
      · simp
      · intro i hi hi'
        simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
        have hBound : i < q.n := by simpa using hi'
        change gridPoint (context q) i = q.grid ⟨i, hBound⟩
        have h := hRaw ⟨i, hBound⟩
        unfold gridPoint
        rw [h]
        simp only [context, AnchoredPriceRequest.grid, Nat.cast_pow, Nat.cast_ofNat]
    have hWire : (List.map (encodeRat ∘ (fun z : ℤ => (z : ℚ)))
        (List.ofFn q.grid)).flatten = encodeGrid q.grid := by
      rw [← List.map_map, List.map_ofFn]
      rfl
    change frame (evaluationPacket q) ++ encodeRat (rawPoint (context q) q.designated.val) = q.encodeResult
    rw [hRaw q.designated]
    simp only [evaluationPacket, AnchoredPriceRequest.encodeResult, dyadicQuery, hGrid, hWire, List.append_assoc])


namespace AnchoredPriceRequest

theorem binary : BitPolynomial AnchoredPriceRequest.encode (fun q output => output = q.encodeResult) := by
  exact bitPolynomial_of_procedure anchoredRequestProcedure

end AnchoredPriceRequest

end EF1FPO
