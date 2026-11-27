import EF1FPO.GraphMath
import EF1FPO.EvaluatorProgram
import EF1FPO.EvaluationParameters

/-! Native finite stack comparisons of all positive bidders in the exact tie window. -/

set_option autoImplicit false

namespace EF1FPO.GreatestGraphStage

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open EvaluationWire
open PreparationMatrixWire (readCell)
open PricePacketProcedures

noncomputable def queryFromGuessProcedure : Procedure Guess.encode EvaluationInput.encode Guess.asQuery := by
  let fields (g : Guess) : Instance × (ℕ × Word) := (g.prepared.inst, g.precision, encodeGrid g.grid)
  let prepared := (first encodeInstance rawUnaryField).precompose fields
  let rest := (second encodeInstance rawUnaryField).precompose fields
  let read := decodeUnaryField.comp rest
  let s := (first unaryCode id).comp read
  let numerator := (second unaryCode id).comp read
  let digits := s.result (ec := id) (h := fun g => unaryCode g.precision) (fun _ => rfl)
  let suffix : Procedure (prodCode encodeInstance rawUnaryField ∘ fields) id
      (fun g => [false, false] ++ encodeGrid g.grid) :=
    ((Procedure.prepend id [false, false]).comp numerator).result (fun _ => rfl)
  let fieldsWithOutput := Procedure.append.comp (digits.pair suffix)
  let word := prepared.pair fieldsWithOutput
  let typed : Procedure (prodCode encodeInstance rawUnaryField ∘ fields)
      EvaluationInput.encode Guess.asQuery := word.result (by
    intro g
    simp [Function.comp_apply, fields, prodCode, pairBits, quoteBits_eq_frame,
      Guess.asQuery, EvaluationInput.encode, dyadicQuery, unaryCode, encodeUnary, List.append_assoc])
  exact typed.congrEncoding (by
    intro g
    simp [fields, Guess.encode, rawUnaryField, encodeUnary, prodCode, pairBits, quoteBits_eq_frame,
      List.append_assoc]) (fun _ => rfl)

abbrev BidData := (ℕ × ℕ) × (ℕ × (ℚ × (RationalRows × List ℚ)))

def bidDataCode : BidData → Word :=
  prodCode (prodCode unaryCode unaryCode)
    (prodCode unaryCode (prodCode ratCode (prodCode rowsCode ratsCode)))

def bidData (d : EvaluationData) : BidData :=
  let p := tableHeight d.1
  ((d.1.1, d.1.2.1), 7 * p, ((2 : ℚ) ^ (4 * p))⁻¹, d.1.2.2.2, queryScaledPoint d)

def flag (d : BidData) (i j : ℕ) : Bool :=
  let t := d.2.1
  let tolerance := d.2.2.1
  let rows := d.2.2.2.1
  let z := d.2.2.2.2
  let own := readCell 0 (readCell [] rows i) j
  let seed := readCell 0 z i
  let p : RivalData := ((i, j), t, seed, rows, z)
  decide (0 < own ∧ maximum ((List.range d.1.1).map (rivalAt p), seed) ≤ seed + tolerance)

def bidderFlags (d : BidData) : List (List Bool) :=
  (List.range d.1.1).map fun i => (List.range d.1.2).map (flag d i)

noncomputable def bidDataProcedure : Procedure dataCode bidDataCode bidData := by
  let vectorCode := prodCode unaryCode (prodCode unaryCode ratsCode)
  let table := first tableCode vectorCode
  let vectors := second tableCode vectorCode
  let source := (first unaryCode (prodCode unaryCode ratsCode)).comp vectors
  let grid := (second unaryCode ratsCode).comp ((second unaryCode (prodCode unaryCode ratsCode)).comp vectors)
  let n := (first unaryCode tableTailCode).comp table
  let rest := (second unaryCode tableTailCode).comp table
  let m := (first unaryCode matrixTailCode).comp rest
  let valuations := (second unaryCode rowsCode).comp ((second unaryCode matrixTailCode).comp rest)
  let P := tableHeightProcedure.comp table
  let t := unaryMul.comp ((constant dataCode unaryCode 7).pair P)
  let s := unaryMul.comp ((constant dataCode unaryCode 4).pair P)
  let rs := tableRadiusProcedure.comp table
  let zn := scaleListProcedure.comp (source.pair (rs.pair grid))
  let lattice := natToRat.comp (powTwo.comp s)
  let τ := ratDiv.comp ((constant dataCode ratCode (1 : ℚ)).pair lattice)
  exact ((n.pair m).pair (t.pair (τ.pair (valuations.pair zn)))).congrFun (by
    intro d
    change ((d.1.1, d.1.2.1), 7 * tableHeight d.1,
      (1 : ℚ) / (((2 : ℕ) ^ (4 * tableHeight d.1) : ℕ) : ℚ), d.1.2.2.2,
      scaleList (d.2.1, tableRadius d.1, d.2.2.2)) = bidData d
    rw [bidData, Nat.cast_pow, Nat.cast_ofNat, one_div]
    rfl)

section
attribute [local irreducible] flag rivalAtProcedure maximumProcedure guardedLog

set_option maxHeartbeats 500000 in
noncomputable def bidderFlagsProcedure :
    Procedure bidDataCode (listCode (listCode boolCode)) bidderFlags := by
  let dimsCode := prodCode unaryCode unaryCode
  let tablesCode := prodCode rowsCode ratsCode
  let numericCode := prodCode ratCode tablesCode
  let payloadCode := prodCode unaryCode numericCode
  let dimensions := first dimsCode payloadCode
  let n := (first unaryCode unaryCode).comp dimensions
  let m := (second unaryCode unaryCode).comp dimensions
  let other := second dimsCode payloadCode
  let t := (first unaryCode numericCode).comp other
  let numericPart := (second unaryCode numericCode).comp other
  let τ := (first ratCode tablesCode).comp numericPart
  let tables := (second ratCode tablesCode).comp numericPart
  let rows := (first rowsCode ratsCode).comp tables
  let z := (second rowsCode ratsCode).comp tables
  let row := prodCode unaryCode bidDataCode
  let source := prodCode unaryCode row
  let j := unaryToBits.comp (first unaryCode row)
  let rest := second unaryCode row
  let i := unaryToBits.comp ((first unaryCode bidDataCode).comp rest)
  let d := (second unaryCode bidDataCode).comp rest
  let seed := (listGet ratCode (0 : ℚ)).comp (i.pair (z.comp d))
  let mainRow := (listGet ratsCode ([] : List ℚ)).comp (i.pair (rows.comp d))
  let own := (listGet ratCode (0 : ℚ)).comp (j.pair mainRow)
  let args := (i.pair j).pair ((t.comp d).pair (seed.pair (tables.comp d)))
  let enumerated := (tabulate (ea := rivalCode) (eb := ratCode) (f := rivalAt) (0 : ℚ)
    rivalAtProcedure).comp ((n.comp d).pair args)
  let best := maximumProcedure.comp (enumerated.pair seed)
  let ceiling := ratAdd.comp (seed.pair (τ.comp d))
  let within := Arithmetic.ratLe.comp (best.pair ceiling)
  let owned := Arithmetic.ratLt.comp ((constant source ratCode (0 : ℚ)).pair own)
  let test : Procedure source boolCode (fun x => flag x.2.2 x.2.1 x.1) :=
    (boolAnd.comp (owned.pair within)).congrFun (by
      intro x
      rw [Bool.eq_iff_iff]
      simp [Function.comp_apply, flag, readCell])
  let assemble (testCell : BidData → ℕ → ℕ → Bool)
      (machine : Procedure source boolCode (fun x => testCell x.2.2 x.2.1 x.1)) :
      Procedure bidDataCode (listCode (listCode boolCode)) (fun d =>
        (List.range d.1.1).map fun i => (List.range d.1.2).map (testCell d i)) := by
    let rowMask : Procedure row (listCode boolCode)
        (fun d => (List.range d.2.1.2).map (testCell d.2 d.1)) :=
      (tabulate (ea := row) (eb := boolCode)
        (f := fun x g => testCell x.2 x.1 g) false machine).comp
          ((m.comp (second unaryCode bidDataCode)).pair (identity row))
    let mask := (tabulate (ea := bidDataCode) (eb := listCode boolCode)
      (f := fun d i => (List.range d.1.2).map (testCell d i)) [] rowMask).comp
        (n.pair (identity bidDataCode))
    exact mask.congrFun (fun d => by simp only [Function.comp_apply, id_eq])
  exact assemble flag test

end

theorem bidderFlags_agree (d : Guess) :
    bidderFlags (bidData (decodeEvaluation d.asQuery)) = List.ofFn (fun i => List.ofFn (d.mask i)) := by
  classical
  let I := d.prepared.inst
  let P := weightBits I
  let t := 7 * P
  let τ := ((2 : ℚ) ^ (4 * P))⁻¹
  let rows := List.ofFn (fun i : I.Agent => List.ofFn (I.v i))
  let z := d.asQuery.scaledPoint
  have lookup {A : Type} {n : ℕ} (fallback : A) (f : Fin n → A) (i : Fin n) :
      readCell fallback (List.ofFn f) i.val = f i := by
    rw [readCell, List.headD_eq_head?_getD, List.head?_drop,
      List.getElem?_eq_getElem (by simp), Option.getD_some]
    simp
  have mapRange {A : Type} {n : ℕ} (f : ℕ → A) (q : Fin n → A)
      (h : ∀ i, f i.val = q i) : (List.range n).map f = List.ofFn q := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
      exact h ⟨i, by simpa using hi'⟩
  have maxSpec (xs : List ℚ) (seed limit : ℚ) :
      maximum (xs, seed) ≤ limit ↔ seed ≤ limit ∧ ∀ q ∈ xs, q ≤ limit := by
    induction xs generalizing seed with
    | nil => simp [maximum]
    | cons x xs ih =>
      change maximum (xs, max x seed) ≤ limit ↔ seed ≤ limit ∧ ∀ q ∈ x :: xs, q ≤ limit
      simp only [ih, max_le_iff, List.forall_mem_cons]
      tauto
  have scaled : queryScaledPoint (decodeEvaluation d.asQuery) = List.ofFn z := by
    simp [queryScaledPoint, decodeEvaluation, table, z, EvaluationInput.scaledPoint,
      logRadius, I, List.map_ofFn, Function.comp_apply]
    funext i
    simp [Function.comp_apply, EvaluationInput.scaledPoint, logRadius, Nat.cast_mul, Nat.cast_add]
  have dataEq : bidData (decodeEvaluation d.asQuery) = ((I.n, I.m), t, τ, rows, List.ofFn z) := by
    unfold bidData
    rw [scaled]
    rfl
  rw [dataEq]
  unfold bidderFlags
  apply mapRange
  intro i
  apply mapRange
  intro g
  let p : RivalData := ((i.val, g.val), t, z i, rows, List.ofFn z)
  have nonneg : 0 ≤ τ := by dsimp [τ]; positivity
  have seedLe : z i ≤ z i + τ := by linarith only [nonneg]
  have evaluated (k : I.Agent) : readCell 0 (List.ofFn z) k.val = z k := lookup 0 z k
  have formula (k : I.Agent) : rivalAt p k.val =
      if k ≠ i ∧ 0 < I.v k g then
        max (z i) (z k + guardedLog (I.v k g) t - guardedLog (I.v i g) t)
      else z i := by
    simp only [rivalAt, p, rows, lookup, evaluated, ne_eq, Fin.val_inj]
  simp only [flag, rows, lookup, evaluated, Guess.mask, decide_eq_decide]
  change (0 < I.v i g ∧ maximum ((List.range I.n).map (rivalAt p), z i) ≤ z i + τ) ↔ _
  rw [maxSpec]
  constructor
  · rintro ⟨hi, _, eligible⟩
    refine ⟨hi, fun k hk => ?_⟩
    by_cases eq : k = i
    · subst k
      simpa only [sub_self] using nonneg
    · have mem : rivalAt p k.val ∈ (List.range I.n).map (rivalAt p) :=
        List.mem_map.mpr ⟨k.val, List.mem_range.mpr k.isLt, rfl⟩
      have limit := eligible _ mem
      rw [formula, if_pos ⟨eq, hk⟩] at limit
      have h := (max_le_iff.mp limit).2
      change (z k + guardedLog (I.v k g) t) - (z i + guardedLog (I.v i g) t) ≤ τ
      linarith only [h]
  · rintro ⟨hi, eligible⟩
    refine ⟨hi, seedLe, fun u hu => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hu
    let k : I.Agent := ⟨j, List.mem_range.mp hj⟩
    change rivalAt p k.val ≤ z i + τ
    rw [formula]
    by_cases positive : k ≠ i ∧ 0 < I.v k g
    · have h := eligible k positive.2
      change (z k + guardedLog (I.v k g) t) - (z i + guardedLog (I.v i g) t) ≤ τ at h
      exact (if_pos positive).trans_le (max_le seedLe (by linarith only [h]))
    · exact (if_neg positive).trans_le seedLe

noncomputable def maskProcedure : Procedure Guess.encode id (fun g => encodeBidderMask g.mask) := by
  let bits := bidderFlagsProcedure.comp (bidDataProcedure.comp
    (decodeEvaluationProcedure.comp queryFromGuessProcedure))
  let writeBit : Procedure boolCode id (fun b => [b]) := (identity boolCode).result (fun _ => rfl)
  let row : Procedure (listCode boolCode) id id :=
    (Wire.flatten.comp (Procedure.listMap false ([] : Word) writeBit)).congrFun (by
      intro xs
      induction xs with
      | nil => rfl
      | cons v xs ih => simpa only [Function.comp_apply, List.map_cons, List.flatten_cons,
          List.singleton_append, id_eq, List.cons.injEq, true_and] using ih)
  let writeRows := Procedure.listMap ([] : List Bool) ([] : Word) row
  exact (Wire.flatten.comp (writeRows.comp bits)).congrFun (by
    intro g
    simp only [Function.comp_apply, List.map_id, id_eq, encodeBidderMask, bidderFlags_agree])

end EF1FPO.GreatestGraphStage
