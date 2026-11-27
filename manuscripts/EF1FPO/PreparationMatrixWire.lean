import EF1FPO.PreparationArithmeticWire
import OAI.Optimization.LinearProgramming.OracleSpec.PriceEncoding
import OAI.Optimization.LinearProgramming.PriceGame.LearningGroupingSort

/-! Packed matrices, retained columns, and exact integer rows for preparation. -/

set_option autoImplicit false

namespace EF1FPO.PreparationMatrixWire

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.Optimization.LinearProgramming.PriceGame
open EF1FPO.PreparationArithmeticWire (scaleRow scaleRowProcedure scaleRow_retained_entry)

abbrev Packed := ℕ × ℕ × List ℚ
abbrev Rows := List (List ℚ)
abbrev IntegerRows := List (List ℕ)

def packedCode : Packed → Word := prodCode unaryCode (prodCode unaryCode (listCode ratCode))
def rowsCode : Rows → Word := listCode (listCode ratCode)
def integerRowsCode : IntegerRows → Word := listCode (listCode Nat.bits)

def readCell {α : Type} (fallback : α) (xs : List α) (i : ℕ) : α := (xs.drop i).headD fallback

def unpackRow (p : ℕ × List ℚ) (i : ℕ) : List ℚ :=
  (List.range p.1).map (fun g => readCell 0 p.2 (i * p.1 + g))

def unpackRows (p : Packed) : Rows := (List.range p.1).map (unpackRow p.2)

noncomputable def unpackRowsProcedure : Procedure packedCode rowsCode unpackRows := by
  let rowCode := listCode ratCode
  let source := prodCode unaryCode rowCode
  let withOffset := prodCode Nat.bits rowCode
  let colIndex := unaryToBits.comp (first unaryCode withOffset)
  let portion := second unaryCode withOffset
  let offset := (first Nat.bits rowCode).comp portion
  let values := (second Nat.bits rowCode).comp portion
  let absolute := binaryAdd.comp (offset.pair colIndex)
  let cell := (listGet ratCode 0).comp (absolute.pair values)
  let across := tabulate (ea := withOffset) (eb := ratCode)
    (f := fun p g => readCell 0 p.2 (p.1 + g)) 0 cell
  let rowIndex := unaryToBits.comp (first unaryCode source)
  let given := second unaryCode source
  let width := (first unaryCode rowCode).comp given
  let readData := (second unaryCode rowCode).comp given
  let start := binaryMul.comp (rowIndex.pair (unaryToBits.comp width))
  let row : Procedure (prodCode unaryCode source) rowCode (fun p => unpackRow p.2 p.1) :=
    (across.comp (width.pair (start.pair readData))).congrFun (by intro p; rfl)
  exact (tabulate (ea := source) (eb := rowCode) (f := unpackRow) [] row).congrFun (by intro p; rfl)

def keepColumn (rows : Rows) (g : ℕ) : Bool :=
  !(rows.filter fun row => decide (0 < readCell 0 row g)).isEmpty

def keptColumns (p : ℕ × Rows) : List ℕ := (List.range p.1).filter (keepColumn p.2)

noncomputable def keptColumnsProcedure :
    Procedure (prodCode unaryCode rowsCode) (listCode Nat.bits) keptColumns := by
  let rowCode := listCode ratCode
  let testCode := prodCode Nat.bits rowCode
  let value := listGet ratCode 0
  let positive := Arithmetic.ratLt.comp ((constant testCode ratCode 0).pair value)
  let passing := Learning.BitMachine.filterWithP ([] : List ℚ) positive
  let test : Procedure (prodCode rowsCode Nat.bits) boolCode (fun p => keepColumn p.1 p.2) :=
    (boolNot.comp ((listEmpty rowCode).comp passing)).congrFun (by intro p; rfl)
  let remaining := Learning.BitMachine.filterWithP (0 : ℕ) test
  let columnCount := first unaryCode rowsCode
  let all := Control.Native.addressRangeP.comp columnCount
  exact (remaining.comp (all.pair (second unaryCode rowsCode))).congrFun (by intro p; rfl)

def selectScaledRow (keys : List ℕ) (raw : List ℚ) : List ℕ :=
  keys.map (readCell 0 (scaleRow raw))

def scaledRetainedRows (p : Rows × List ℕ) : IntegerRows := p.1.map (selectScaledRow p.2)

noncomputable def scaledRetainedRowsProcedure :
    Procedure (prodCode rowsCode (listCode Nat.bits)) integerRowsCode scaledRetainedRows := by
  let keys := listCode Nat.bits
  let rowCode := listCode ratCode
  let lookup := (listGet Nat.bits 0).comp (swap keys Nat.bits)
  let select := Market.GridMachine.mapWithContext (0 : ℕ) (0 : ℕ) lookup
  let keysIn := first keys rowCode
  let scaled := scaleRowProcedure.comp (second keys rowCode)
  let row : Procedure (prodCode keys rowCode) keys (fun p => selectScaledRow p.1 p.2) :=
    (select.comp (keysIn.pair scaled)).congrFun (by intro p; rfl)
  exact (Market.GridMachine.mapWithContext ([] : List ℚ) ([] : List ℕ) row).congrFun (by intro p; rfl)

private theorem readCell_eq_getElem? {α : Type} (d : α) (xs : List α) (j : ℕ) :
    readCell d xs j = xs[j]?.getD d := by
  rw [readCell, List.headD_eq_head?_getD, List.head?_drop]

private theorem readCell_ofFn {α : Type} {n : ℕ} (d : α) (f : Fin n → α) (i : Fin n) :
    readCell d (List.ofFn f) i.val = f i := by
  rw [readCell_eq_getElem?, List.getElem?_eq_getElem (by simp), Option.getD_some]
  simp

theorem unpackRows_agrees (I : Instance) :
    let rows := List.ofFn (fun i : I.Agent => List.ofFn (I.v i))
    unpackRows (I.n, I.m, rows.flatten) = rows := by
  let rows := List.ofFn (fun i : I.Agent => List.ofFn (I.v i))
  let f (z : Fin (I.n * I.m)) : ℚ := I.v (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2
  have index (i : I.Agent) (g : I.Good) : (finProdFinEquiv (i, g)).val = i.val * I.m + g.val := by
    change g.val + I.m * i.val = _
    ac_rfl
  have flat : rows.flatten = List.ofFn f := by
    rw [List.ofFn_mul]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    apply congrArg List.ofFn
    funext g
    have equal (z : Fin (I.n * I.m)) (h : z.val = i.val * I.m + g.val) :
        finProdFinEquiv.symm z = (i, g) := by
      apply finProdFinEquiv.injective
      rw [Equiv.apply_symm_apply]
      exact Fin.ext (h.trans (index i g).symm)
    exact (congrArg (fun p : I.Agent × I.Good => I.v p.1 p.2)
      (equal _ (by simp))).symm
  have read (i : I.Agent) (g : I.Good) :
      readCell 0 rows.flatten (i.val * I.m + g.val) = I.v i g := by
    rw [flat, ← index i g, readCell_ofFn]
    exact congrArg (fun p : I.Agent × I.Good => I.v p.1 p.2)
      (finProdFinEquiv.symm_apply_apply (i, g))
  change unpackRows (I.n, I.m, rows.flatten) = rows
  apply List.ext_getElem
  · simp [unpackRows, rows]
  · intro i _ hi
    let a : I.Agent := ⟨i, by simpa only [rows, List.length_ofFn] using hi⟩
    simp only [unpackRows, List.getElem_map, List.getElem_range, rows, List.getElem_ofFn]
    change unpackRow (I.m, rows.flatten) a.val = List.ofFn (I.v a)
    apply List.ext_getElem
    · simp [unpackRow]
    · intro g _ hg
      let k : I.Good := ⟨g, by simpa only [List.length_ofFn] using hg⟩
      simp only [unpackRow, List.getElem_map, List.getElem_range, List.getElem_ofFn]
      exact read a k

theorem keptColumns_agrees {I : Instance} (P : Preparation I) (h : P.IsPreparation) :
    keptColumns (I.m, List.ofFn (fun i : I.Agent => List.ofFn (I.v i))) =
      List.ofFn (fun g => (P.keptGood g).val) := by
  let rows := List.ofFn (fun i : I.Agent => List.ofFn (I.v i))
  have selected (g : I.Good) : keepColumn rows g.val = true ↔ ∃ i, 0 < I.v i g := by
    let qualifying := rows.filter fun r => decide (0 < readCell 0 r g.val)
    have test : keepColumn rows g.val = !qualifying.isEmpty := rfl
    rw [test]
    constructor
    · intro hm
      have hExists : ∃ row, row ∈ qualifying := by
        cases hList : qualifying with
        | nil => simp [hList] at hm
        | cons a as => exact ⟨a, List.mem_cons_self⟩
      obtain ⟨row, hrow⟩ := hExists
      obtain ⟨hr, hp⟩ := List.mem_filter.mp hrow
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
      exact ⟨i, by simpa only [decide_eq_true_eq, readCell_ofFn] using hp⟩
    · rintro ⟨i, hi⟩
      have hMem : List.ofFn (I.v i) ∈ qualifying := List.mem_filter.mpr
        ⟨List.mem_ofFn.mpr ⟨i, rfl⟩, by simp [readCell_ofFn, hi]⟩
      cases hm : qualifying with
      | nil => simp [hm] at hMem
      | cons a as => simp [hm]
  let K := keptColumns (I.m, rows)
  let K' := List.ofFn (fun k => (P.keptGood k).val)
  have hK : K.SortedLT := ((List.sortedLT_range _).pairwise.filter _).sortedLT
  have hK' : K'.SortedLT := List.sortedLT_ofFn_iff.mpr (fun _ _ hb => h.1 hb)
  apply List.Perm.eq_of_sortedLE hK.sortedLE hK'.sortedLE
  apply (List.perm_ext_iff_of_nodup hK.nodup hK'.nodup).mpr
  intro g
  constructor
  · intro hg
    obtain ⟨hRange, hPos⟩ := List.mem_filter.mp hg
    let f : I.Good := ⟨g, List.mem_range.mp hRange⟩
    obtain ⟨k, hk⟩ := (h.2.1 f).mpr ((selected f).mp hPos)
    exact List.mem_ofFn.mpr ⟨k, congrArg Fin.val hk⟩
  · intro hg
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (P.keptGood k).isLt,
      (selected _).mpr ((h.2.1 _).mp ⟨k, rfl⟩)⟩

theorem scaledRetainedRows_agrees {I : Instance} (P : Preparation I) :
    scaledRetainedRows (List.ofFn (fun i : I.Agent => List.ofFn (I.v i)),
      List.ofFn (fun g => (P.keptGood g).val)) =
      List.ofFn (fun i : I.Agent => List.ofFn (P.scaled i)) := by
  simp only [scaledRetainedRows, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply, selectScaledRow, List.map_ofFn]
  apply congrArg List.ofFn
  funext g
  dsimp only [Function.comp_apply]
  rw [readCell_eq_getElem?, scaleRow_retained_entry, Option.getD_some]

end EF1FPO.PreparationMatrixWire
