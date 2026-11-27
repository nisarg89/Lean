import EF1FPO.EvaluationPrimitives
import EF1FPO.EvaluationWire
import EF1FPO.EvaluationParameters

/-! Native bit-stack cutoff enumeration on one decoded table. -/

set_option autoImplicit false

namespace EF1FPO.EvaluationWire

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.Optimization.LinearProgramming.PriceGame.Control.Native
open OAI.Optimization.LinearProgramming.PriceGame.Market.GridMachine (mapWithContext)
open PreparationMatrixWire (readCell)

abbrev RationalRows := List (List ℚ)
def rowsCode : RationalRows → Word := listCode (listCode ratCode)
def ratsCode : List ℚ → Word := listCode ratCode

abbrev RivalData := (ℕ × ℕ) × (ℕ × (ℚ × (RationalRows × List ℚ)))

def rivalCode : RivalData → Word :=
  prodCode (prodCode Nat.bits Nat.bits)
    (prodCode unaryCode (prodCode ratCode (prodCode rowsCode ratsCode)))

def rivalAt (p : RivalData) (j : ℕ) : ℚ :=
  let i := p.1.1
  let g := p.1.2
  let t := p.2.1
  let floor := p.2.2.1
  let rows := p.2.2.2.1
  let z := p.2.2.2.2
  let own := readCell 0 (readCell [] rows i) g
  let rival := readCell 0 (readCell [] rows j) g
  if j ≠ i ∧ 0 < rival then
    max floor (readCell 0 z j + guardedLog rival t - guardedLog own t)
  else floor

noncomputable def rivalAtProcedure :
    Procedure (prodCode unaryCode rivalCode) ratCode (fun x => rivalAt x.2 x.1) := by
  let code := prodCode unaryCode rivalCode
  let indexCode := prodCode Nat.bits Nat.bits
  let tablesCode := prodCode rowsCode ratsCode
  let floorCode := prodCode ratCode tablesCode
  let restCode := prodCode unaryCode floorCode
  let j := unaryToBits.comp (first unaryCode rivalCode)
  let data := second unaryCode rivalCode
  let addresses := (first indexCode restCode).comp data
  let i := (first Nat.bits Nat.bits).comp addresses
  let g := (second Nat.bits Nat.bits).comp addresses
  let rest := (second indexCode restCode).comp data
  let t := (first unaryCode floorCode).comp rest
  let floorData := (second unaryCode floorCode).comp rest
  let floor := (first ratCode tablesCode).comp floorData
  let tables := (second ratCode tablesCode).comp floorData
  let rows := (first rowsCode ratsCode).comp tables
  let z := (second rowsCode ratsCode).comp tables
  let getRow := listGet (listCode ratCode) ([] : List ℚ)
  let getCell := listGet ratCode (0 : ℚ)
  let own := getCell.comp (g.pair (getRow.comp (i.pair rows)))
  let rival := getCell.comp (g.pair (getRow.comp (j.pair rows)))
  let coordinate := getCell.comp (j.pair z)
  let ownLog := guardedLogProcedure.comp (own.pair t)
  let rivalLog := guardedLogProcedure.comp (rival.pair t)
  let score := ratSub.comp ((ratAdd.comp (coordinate.pair rivalLog)).pair ownLog)
  let capped := ratMaxP.comp (floor.pair score)
  let different := boolNot.comp (natEqP.comp (j.pair i))
  let positive := Arithmetic.ratLt.comp ((constant code ratCode (0 : ℚ)).pair rival)
  let condition := boolAnd.comp (different.pair positive)
  exact (conditional condition capped floor).congrFun (by
    intro x
    by_cases hEq : x.1 = x.2.1.1 <;>
      by_cases hPos : 0 < readCell 0 (readCell [] x.2.2.2.2.1 x.1) x.2.1.2 <;>
      simp [rivalAt, readCell, Function.comp_apply, hEq, hPos])

abbrev RowData := (ℕ × ℕ) × (RationalRows × List ℚ)

def rowCode : RowData → Word :=
  prodCode (prodCode Nat.bits unaryCode) (prodCode rowsCode ratsCode)

def rowOwn (p : RowData) : List ℚ := readCell [] p.2.1 p.1.1

def rowRivalData (p : RowData) (g : ℕ) : RivalData :=
  ((p.1.1, g), p.1.2, -guardedLog (rowOwn p).sum p.1.2, p.2.1, p.2.2)

def rowLevel (p : RowData) (g : ℕ) : ℚ :=
  let d := rowRivalData p g
  maximum ((List.range p.2.1.length).map (rivalAt d), d.2.2.1)

def rowLevels (p : RowData) : List ℚ := (List.range (rowOwn p).length).map (rowLevel p)

noncomputable def rowLevelsProcedure : Procedure rowCode ratsCode rowLevels := by
  let metadata := prodCode Nat.bits unaryCode
  let matrices := prodCode rowsCode ratsCode
  let indices := first metadata matrices
  let i := (first Nat.bits unaryCode).comp indices
  let t := (second Nat.bits unaryCode).comp indices
  let data := second metadata matrices
  let rows := (first rowsCode ratsCode).comp data
  let own := (listGet (listCode ratCode) ([] : List ℚ)).comp (i.pair rows)
  let seed := ratNeg.comp (guardedLogProcedure.comp ((ratListSumP.comp own).pair t))
  let outSize := (rowSizeP ratCode (0 : ℚ)).comp own
  let inSize := (rowSizeP (listCode ratCode) ([] : List ℚ)).comp rows
  let extract := second unaryCode rowCode
  let g := unaryToBits.comp (first unaryCode rowCode)
  let fields := ((i.comp extract).pair g).pair
    ((t.comp extract).pair ((seed.comp extract).pair (data.comp extract)))
  let inner := tabulate (ea := rivalCode) (eb := ratCode) (f := rivalAt) (0 : ℚ) rivalAtProcedure
  let rivals := inner.comp ((inSize.comp extract).pair fields)
  let cell : Procedure (prodCode unaryCode rowCode) ratCode (fun x => rowLevel x.2 x.1) :=
    (maximumProcedure.comp (rivals.pair (seed.comp extract))).congrFun (fun _ => rfl)
  exact ((tabulate (ea := rowCode) (eb := ratCode) (f := rowLevel) (0 : ℚ) cell).comp
    (outSize.pair (identity rowCode))).congrFun (fun _ => rfl)

abbrev ScoreData := ℕ × (List ℚ × List ℚ)

def scoreCode : ScoreData → Word := prodCode unaryCode (prodCode ratsCode ratsCode)

def cutoffEntry (p : ScoreData) (level : ℚ) (g : ℕ) : ℚ :=
  if readCell 0 p.2.2 g ≤ level then readCell 0 p.2.1 g else 0

def candidateScore (p : ScoreData) (g : ℕ) : ℚ :=
  let own := readCell 0 p.2.1 g
  let level := readCell 0 p.2.2 g
  let selected := (List.range p.2.1.length).map (cutoffEntry p level)
  if 0 < own then max (-guardedLog selected.sum p.1) level else guardedLog 4 p.1

noncomputable def candidateScoreProcedure :
    Procedure (prodCode unaryCode scoreCode) ratCode (fun x => candidateScore x.2 x.1) := by
  let code := prodCode unaryCode scoreCode
  let rowPair := prodCode ratsCode ratsCode
  let d := second unaryCode scoreCode
  let g := unaryToBits.comp (first unaryCode scoreCode)
  let t := (first unaryCode rowPair).comp d
  let rows := (second unaryCode rowPair).comp d
  let values := (first ratsCode ratsCode).comp rows
  let levels := (second ratsCode ratsCode).comp rows
  let get := listGet ratCode (0 : ℚ)
  let v := get.comp (g.pair values)
  let level := get.comp (g.pair levels)
  let context := prodCode rowPair ratCode
  let entryCode := prodCode unaryCode context
  let j := unaryToBits.comp (first unaryCode context)
  let extra := second unaryCode context
  let lookups := (first rowPair ratCode).comp extra
  let chosen := (second rowPair ratCode).comp extra
  let eachValue := get.comp (j.pair ((first ratsCode ratsCode).comp lookups))
  let eachLevel := get.comp (j.pair ((second ratsCode ratsCode).comp lookups))
  let below := Arithmetic.ratLe.comp (eachLevel.pair chosen)
  let entry : Procedure entryCode ratCode
      (fun x => if readCell 0 x.2.1.2 x.1 ≤ x.2.2 then readCell 0 x.2.1.1 x.1 else 0) :=
    (conditional below eachValue (constant entryCode ratCode (0 : ℚ))).congrFun (by
      intro x
      simp [readCell, Function.comp_apply])
  let m := (rowSizeP ratCode (0 : ℚ)).comp values
  let selected := (tabulate (ea := context) (eb := ratCode)
    (f := fun row j => if readCell 0 row.1.2 j ≤ row.2 then readCell 0 row.1.1 j else 0)
    (0 : ℚ) entry).comp (m.pair (rows.pair level))
  let sum := ratListSumP.comp selected
  let logCost := ratNeg.comp (guardedLogProcedure.comp (sum.pair t))
  let high := ratMaxP.comp (logCost.pair level)
  let cap := guardedLogProcedure.comp ((constant code ratCode (4 : ℚ)).pair t)
  let positive := Arithmetic.ratLt.comp ((constant code ratCode (0 : ℚ)).pair v)
  exact (conditional positive high cap).congrFun (by
    intro x
    simp only [Function.comp_apply, id_eq, decide_eq_true_eq, candidateScore, readCell]
    rfl)

def rowCapped (p : RowData) : ℚ :=
  let own := rowOwn p
  let data := (p.1.2, own, rowLevels p)
  minimum ((List.range own.length).map (candidateScore data), guardedLog 4 p.1.2)

section
attribute [local irreducible] rowLevelsProcedure candidateScoreProcedure guardedLogProcedure guardedLog
  minimumProcedure

noncomputable def rowCappedProcedure : Procedure rowCode ratCode rowCapped := by
  let build (capLog : ℚ × ℕ → ℚ) (capLogP : Procedure logPairCode ratCode capLog)
      (levels : RowData → List ℚ) (levelP : Procedure rowCode ratsCode levels)
      (score : ScoreData → ℕ → ℚ)
      (scoreP : Procedure (prodCode unaryCode scoreCode) ratCode (fun x => score x.2 x.1)) :
      Procedure rowCode ratCode (fun p => minimum
        ((List.range (rowOwn p).length).map (score (p.1.2, rowOwn p, levels p)), capLog (4, p.1.2))) := by
    let metadata := prodCode Nat.bits unaryCode
    let matrices := prodCode rowsCode ratsCode
    let indices := first metadata matrices
    let i := (first Nat.bits unaryCode).comp indices
    let t := (second Nat.bits unaryCode).comp indices
    let rows := (first rowsCode ratsCode).comp (second metadata matrices)
    let own : Procedure rowCode ratsCode rowOwn :=
      (listGet (listCode ratCode) ([] : List ℚ)).comp (i.pair rows)
    let outSize := (rowSizeP ratCode (0 : ℚ)).comp own
    let given := t.pair (own.pair levelP)
    let enumerated : Procedure rowCode ratsCode (fun p =>
        (List.range (rowOwn p).length).map (score (p.1.2, rowOwn p, levels p))) :=
      (tabulate (ea := scoreCode) (eb := ratCode) (f := score)
      (0 : ℚ) scoreP).comp (outSize.pair given)
    let cap : Procedure rowCode ratCode (fun p => capLog (4, p.1.2)) :=
      capLogP.comp ((constant rowCode ratCode (4 : ℚ)).pair t)
    exact minimumProcedure.comp (enumerated.pair cap)
  exact build (fun a => guardedLog a.1 a.2) guardedLogProcedure
    rowLevels rowLevelsProcedure candidateScore candidateScoreProcedure

end

def queryScaledPoint (d : EvaluationData) : List ℚ :=
  let radius : ℚ := 4 * ((d.1.2.2.1 : ℚ) + 1)
  let inputScale : ℚ := 2 ^ d.2.1
  d.2.2.2.map (fun q => radius * (q / inputScale))

def evaluateCell (d : EvaluationData) (i : ℕ) : ℤ :=
  let r : ℚ := 4 * ((d.1.2.2.1 : ℚ) + 1)
  let t := d.2.2.1 + 4
  let b := 16 * (16 * (d.1.1 + d.1.2.1 + 1) * (d.1.2.2.1 + 1))
  let θ := ((2 : ℚ) ^ b)⁻¹
  let level := rowCapped ((i, t), d.1.2.2.2, queryScaledPoint d)
  roundedNumerator d.2.2.1 (((1 - θ) * level + θ * guardedLog 4 t) / r)

def evaluationList (d : EvaluationData) : List ℤ := (List.range d.1.1).map (evaluateCell d)

set_option maxHeartbeats 1000000 in
noncomputable def evaluationListProcedure :
    Procedure dataCode (listCode intCode) evaluationList := by
  let vectorsCode := prodCode unaryCode (prodCode unaryCode ratsCode)
  let tbl := first tableCode vectorsCode
  let vectors := second tableCode vectorsCode
  let matrix := (second unaryCode rowsCode).comp ((second unaryCode matrixTailCode).comp
    ((second unaryCode tableTailCode).comp tbl))
  let n := (first unaryCode tableTailCode).comp tbl
  let before := (first unaryCode (prodCode unaryCode ratsCode)).comp vectors
  let request := (second unaryCode (prodCode unaryCode ratsCode)).comp vectors
  let after := (first unaryCode ratsCode).comp request
  let numerators := (second unaryCode ratsCode).comp request
  let P := tableHeightProcedure.comp tbl
  let b := unaryMul.comp ((constant dataCode unaryCode 16).pair P)
  let outputPower := natToRat.comp (PricePacketProcedures.powTwo.comp b)
  let θ := ratDiv.comp ((constant dataCode ratCode (1 : ℚ)).pair outputPower)
  let complement := ratSub.comp ((constant dataCode ratCode (1 : ℚ)).pair θ)
  let R := tableRadiusProcedure.comp tbl
  let z := scaleListProcedure.comp (before.pair (R.pair numerators))
  let precision := unaryAdd.comp (after.pair (constant dataCode unaryCode 4))
  let itemCode := prodCode unaryCode dataCode
  let datum := second unaryCode dataCode
  let i := unaryToBits.comp (first unaryCode dataCode)
  let readT := precision.comp datum
  let row := (i.pair readT).pair ((matrix.comp datum).pair (z.comp datum))
  let level := rowCappedProcedure.comp row
  let cap := guardedLogProcedure.comp ((constant itemCode ratCode (4 : ℚ)).pair readT)
  let scaled := ratMul.comp ((complement.comp datum).pair level)
  let extra := ratMul.comp ((θ.comp datum).pair cap)
  let value := ratDiv.comp ((ratAdd.comp (scaled.pair extra)).pair (R.comp datum))
  let round := roundedNumeratorProcedure.comp ((after.comp datum).pair value)
  let cell : Procedure itemCode intCode (fun pair => evaluateCell pair.2 pair.1) :=
    round.congrFun (by
      intro x
      simp only [Function.comp_apply, evaluateCell, scaleList, queryScaledPoint, tableRadius,
        tableHeight, Nat.cast_pow, Nat.cast_ofNat, one_div]
      rfl)
  exact (tabulate (ea := dataCode) (eb := intCode) (f := evaluateCell) (0 : ℤ) cell).comp
    (n.pair (identity dataCode))

set_option maxHeartbeats 1000000 in
theorem evaluationList_agrees (d : EvaluationInput) :
    evaluationList (decodeEvaluation d) = List.ofFn d.rounded := by
  classical
  let I := d.prepared.inst
  let t := d.precision + 4
  let values := List.ofFn (fun i : I.Agent => List.ofFn (I.v i))
  let z := d.scaledPoint
  let row (i : I.Agent) : RowData := ((i.val, t), values, List.ofFn z)
  have readFn {A : Type} {n : ℕ} (fallback : A) (a : Fin n → A) (i : Fin n) :
      readCell fallback (List.ofFn a) i.val = a i := by
    rw [readCell, List.headD_eq_head?_getD, List.head?_drop,
      List.getElem?_eq_getElem (by simp), Option.getD_some]
    simp
  have tabulated {A : Type} {n : ℕ} (f : ℕ → A) (q : Fin n → A)
      (h : ∀ i, f i.val = q i) : (List.range n).map f = List.ofFn q := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
      exact h ⟨i, by simpa using hi'⟩
  have maxSpec (xs : List ℚ) (seed bound : ℚ) :
      maximum (xs, seed) ≤ bound ↔ seed ≤ bound ∧ ∀ q ∈ xs, q ≤ bound := by
    induction xs generalizing seed with
    | nil => simp [maximum]
    | cons x xs ih =>
      change maximum (xs, max x seed) ≤ bound ↔ seed ≤ bound ∧ ∀ q ∈ x :: xs, q ≤ bound
      simp only [ih, max_le_iff, List.forall_mem_cons]
      tauto
  have minSpec (xs : List ℚ) (seed bound : ℚ) :
      bound ≤ minimum (xs, seed) ↔ bound ≤ seed ∧ ∀ q ∈ xs, bound ≤ q := by
    induction xs generalizing seed with
    | nil => simp [minimum]
    | cons x xs ih =>
      change bound ≤ minimum (xs, min x seed) ↔ bound ≤ seed ∧ ∀ q ∈ x :: xs, bound ≤ q
      simp only [ih, le_min_iff, List.forall_mem_cons]
      tauto
  have own (i : I.Agent) : rowOwn (row i) = List.ofFn (I.v i) :=
    readFn [] (fun i : I.Agent => List.ofFn (I.v i)) i
  have scale : queryScaledPoint (decodeEvaluation d) = List.ofFn z := by
    simp [queryScaledPoint, decodeEvaluation, table, z, EvaluationInput.scaledPoint,
      logRadius, I, List.map_ofFn, Function.comp_apply]
    funext i
    simp [Function.comp_apply, EvaluationInput.scaledPoint, logRadius, Nat.cast_mul, Nat.cast_add]
  have level (i : I.Agent) (g : I.Good) :
      rowLevel (row i) g.val = rationalRivalLevel I z t i g := by
    let p := rowRivalData (row i) g.val
    let rivals := List.ofFn (fun j : I.Agent => rationalRivalTerm I z t i j g)
    let s := -guardedLog (rowUtility I i Finset.univ) t
    have sumEq : (rowOwn (row i)).sum = rowUtility I i Finset.univ := by
      rw [own]
      exact Fin.sum_ofFn _
    have seedEq : p.2.2.1 = s := by simp [p, rowRivalData, row, s, sumEq]
    have valueEq (j : I.Agent) : rivalAt p j.val = rationalRivalTerm I z t i j g := by
      have hi := readFn [] (fun i : I.Agent => List.ofFn (I.v i)) i
      have hj := readFn [] (fun j : I.Agent => List.ofFn (I.v j)) j
      change rivalAt (((i.val, g.val), t, p.2.2.1, values, List.ofFn z)) j.val = _
      simp only [rivalAt, seedEq, values, hi, hj, readFn, rationalRivalTerm, ne_eq, Fin.val_inj, s]
    have listEq : (List.range (row i).2.1.length).map (rivalAt p) = rivals := by
      rw [show (row i).2.1.length = I.n from List.length_ofFn]
      exact tabulated _ _ valueEq
    change maximum ((List.range (row i).2.1.length).map (rivalAt p), p.2.2.1) = _
    rw [listEq, seedEq]
    let upper := rationalRivalLevel I z t i g
    have lower (j : I.Agent) : rationalRivalTerm I z t i j g ≤ upper :=
      Finset.le_sup' (fun j => rationalRivalTerm I z t i j g) (Finset.mem_univ j)
    have seed : s ≤ upper := by
      simpa [s, rationalRivalTerm] using lower i
    refine le_antisymm ((maxSpec rivals s upper).mpr ⟨seed, ?_⟩) ?_
    · intro q hq
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
      exact lower j
    · apply Finset.sup'_le ⟨i, Finset.mem_univ _⟩
      intro j _
      exact ((maxSpec rivals s (maximum (rivals, s))).mp le_rfl).2 _
        (List.mem_ofFn.mpr ⟨j, rfl⟩)
  have levels (i : I.Agent) : rowLevels (row i) = List.ofFn (rationalRivalLevel I z t i) := by
    unfold rowLevels
    rw [own i, List.length_ofFn]
    exact tabulated _ _ (level i)
  have capped (i : I.Agent) : rowCapped (row i) = cutoffThreshold I z t i := by
    let cap := guardedLog 4 t
    let goods := I.positiveGoods i
    let ranks := rationalRivalLevel I z t i
    let data : ScoreData := (t, List.ofFn (I.v i), List.ofFn ranks)
    let score (g : I.Good) : ℚ :=
      max (-guardedLog (rowUtility I i (cutoff goods ranks g)) t) (ranks g)
    have candidate (g : I.Good) : candidateScore data g.val =
        (if 0 < I.v i g then score g else cap) := by
      have select : ((List.range I.m).map (cutoffEntry data (ranks g))).sum =
          rowUtility I i (cutoff goods ranks g) := by
        let f (j : I.Good) := if ranks j ≤ ranks g then I.v i j else 0
        have listEq : (List.range I.m).map (cutoffEntry data (ranks g)) = List.ofFn f :=
          tabulated _ _ (fun j => by simp [cutoffEntry, data, readFn, f])
        rw [listEq, Fin.sum_ofFn]
        unfold rowUtility
        have zero (j : I.Good) (h : ¬ 0 < I.value i j) : I.v i j = 0 := by
          apply le_antisymm _ (I.nonneg i j)
          by_contra! pos
          exact h (by exact_mod_cast pos)
        rw [show cutoff goods ranks g = Finset.univ.filter
          (fun j => 0 < I.value i j ∧ ranks j ≤ ranks g) from by
          simp [cutoff, goods, Instance.positiveGoods, Finset.filter_filter, and_comm],
          Finset.sum_filter]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        by_cases le : ranks j ≤ ranks g
        · by_cases pos : 0 < I.value i j
          · simp [f, le, pos]
          · simp [f, le, pos, zero j pos]
        · simp [f, le]
      simp [candidateScore, data, readFn, select, cap, score]
    let candidates := List.ofFn (fun g : I.Good => if 0 < I.v i g then score g else cap)
    have packed : (List.range I.m).map (candidateScore data) = candidates :=
      tabulated _ _ candidate
    obtain ⟨g, hg⟩ := d.prepared.preparation.prepared_positive_agents d.prepared.valid i
    have hGood (j : I.Good) : j ∈ goods ↔ 0 < I.v i j := by
      simp [goods, Instance.positiveGoods, Instance.value]
    have goodsNe : goods.Nonempty := ⟨g, (hGood g).mpr hg⟩
    let best := goods.inf' goodsNe score
    have rowEq : rowCapped (row i) = minimum (candidates, cap) := by
      simp only [rowCapped, own, levels, List.length_ofFn]
      change minimum ((List.range I.m).map (candidateScore data), cap) = _
      rw [packed]
    rw [rowEq, cutoffThreshold, dite_eq_left goodsNe]
    change minimum (candidates, cap) = min cap best
    have isLeast := (minSpec candidates cap (minimum (candidates, cap))).mp le_rfl
    refine le_antisymm (le_min isLeast.1 (Finset.le_inf' goodsNe _ ?_))
      ((minSpec candidates cap (min cap best)).mpr ⟨min_le_left _ _, ?_⟩)
    · intro j hj
      have hpos := (hGood j).mp hj
      have hmem : score j ∈ candidates := List.mem_ofFn.mpr ⟨j, by simp [hpos]⟩
      exact isLeast.2 _ hmem
    · intro q hq
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
      by_cases hpos : 0 < I.v i j
      · rw [ite_eq_left hpos]
        exact (min_le_right cap best).trans (Finset.inf'_le score ((hGood j).mpr hpos))
      · rw [ite_eq_right hpos]
        exact min_le_left cap best
  unfold evaluationList
  change (List.range I.n).map (evaluateCell (decodeEvaluation d)) = _
  apply tabulated
  intro i
  have rowMatches : ((i.val, t), (decodeEvaluation d).1.2.2.2,
      queryScaledPoint (decodeEvaluation d)) = row i := by rw [scale]; rfl
  unfold evaluateCell EvaluationInput.rounded EvaluationInput.rawApproximation
  change roundedNumerator d.precision (((1 - _) * rowCapped
    ((i.val, t), (decodeEvaluation d).1.2.2.2, queryScaledPoint (decodeEvaluation d)) + _) / _) = _
  rw [rowMatches, capped]
  simp [decodeEvaluation, table, I, t, z, weightBits, logRadius, Nat.cast_add]

noncomputable def evaluationProcedure :
    Procedure EvaluationInput.encode id (fun d => encodeGrid d.rounded) := by
  let numerators := evaluationListProcedure.comp decodeEvaluationProcedure
  let write := Wire.writeRat.comp intToRat
  let fields := (Procedure.listMap (0 : ℤ) ([] : Word) write).comp numerators
  have serialize (xs : List ℚ) : (xs.map encodeRat).flatten = xs.flatMap encodeRat := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, ih]
  exact (Wire.flatten.comp fields).congrFun (by
    intro d
    simp only [Function.comp_apply, evaluationList_agrees]
    change ((List.ofFn d.rounded).map (encodeRat ∘ (fun z : ℤ => (z : ℚ)))).flatten = _
    rw [← List.map_map, List.map_ofFn, serialize] <;> rfl)

end EF1FPO.EvaluationWire
