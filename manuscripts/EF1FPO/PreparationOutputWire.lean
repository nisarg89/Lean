import EF1FPO.PreparationMatrixWire
import EF1FPO.Computation
import EF1FPO.PricePacketProcedures
import OAI.Optimization.LinearProgramming.OracleSpec.PolynomialFuel
import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCost

/-! Exact perturbation and serialization of the prepared rational table. -/

set_option autoImplicit false

namespace EF1FPO.PreparationOutputWire

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.Optimization.LinearProgramming.PriceGame
open EF1FPO.PreparationArithmeticWire (Summary summaryCode summaryStep summarize powNatural)
open EF1FPO.PreparationMatrixWire (readCell)
open EF1FPO.PricePacketProcedures (powTwo)

abbrev DegreeInput := ℕ × ℕ × ℕ × ℕ

def degreeCode : DegreeInput → Word :=
  prodCode unaryCode (prodCode unaryCode (prodCode unaryCode Nat.bits))

def errorExponent (p : DegreeInput) : ℕ :=
  let (n, k, count, V) := p
  let D := 2 ^ count
  (max (8 * (k + 1) * V * D)
    (max (8 * n * V ^ n * D) (8 * n ^ 2 * D ^ 2))).size

noncomputable def errorExponentProcedure : Procedure degreeCode unaryCode errorExponent := by
  let counts := prodCode unaryCode Nat.bits
  let dimensions := prodCode unaryCode counts
  let n := first unaryCode dimensions
  let rem := second unaryCode dimensions
  let k := (first unaryCode counts).comp rem
  let scales := (second unaryCode counts).comp rem
  let count := (first unaryCode Nat.bits).comp scales
  let maxScale := (second unaryCode Nat.bits).comp scales
  let bN := unaryToBits.comp n
  let bK := unaryToBits.comp (unarySuccessor.comp k)
  let D := powTwo.comp count
  let C := constant degreeCode Nat.bits 8
  let vPow := powNatural.comp (n.pair maxScale)
  let nSq := binaryMul.comp (bN.pair bN)
  let dSq := binaryMul.comp (D.pair D)
  let a := binaryMul.comp ((binaryMul.comp ((binaryMul.comp (C.pair bK)).pair maxScale)).pair D)
  let b := binaryMul.comp ((binaryMul.comp ((binaryMul.comp (C.pair bN)).pair vPow)).pair D)
  let c := binaryMul.comp ((binaryMul.comp (C.pair nSq)).pair dSq)
  let maximum : Procedure (prodCode Nat.bits Nat.bits) Nat.bits (fun p => max p.1 p.2) :=
    (conditional binaryLe (second Nat.bits Nat.bits) (first Nat.bits Nat.bits)).congrFun (by
      rintro ⟨x, y⟩
      by_cases h : x ≤ y
      · simp [h, max_eq_right h]
      · simp [h, max_eq_left (le_of_not_ge h)])
  let maxValue := maximum.comp (a.pair (maximum.comp (b.pair c)))
  exact ((Fuel.lengthInUnary Nat.bits).comp maxValue).congrFun (by
    rintro ⟨n, k, count, v⟩
    change (max (8 * (k + 1) * v * 2 ^ count)
      (max (8 * n * v ^ n * 2 ^ count) (8 * (n * n) * (2 ^ count * 2 ^ count)))).bits.length = _
    simp only [errorExponent, pow_two, Nat.size_eq_bits_len])

def entryCode : ℕ × (ℕ × ℕ) → Word := prodCode Nat.bits (prodCode Nat.bits unaryCode)

def perturbedEntry (p : ℕ × (ℕ × ℕ)) : ℚ :=
  mkRat (p.2.1 * (p.1 + 2 ^ p.2.2) : ℕ) p.1

noncomputable def perturbedEntryProcedure : Procedure entryCode ratCode perturbedEntry := by
  let fields := prodCode Nat.bits unaryCode
  let den := first Nat.bits fields
  let cell := second Nat.bits fields
  let scale := (first Nat.bits unaryCode).comp cell
  let rank := (second Nat.bits unaryCode).comp cell
  let bump := powTwo.comp rank
  let next := binaryAdd.comp (den.pair bump)
  let numerator := natToInt.comp (binaryMul.comp (scale.pair next))
  exact (makeRat.comp (numerator.pair den)).congrFun (by intro p; rfl)

abbrev Input := ℕ × List ℕ × Summary
abbrev Table := ℕ × List ℕ × List ℚ

def inputCode : Input → Word := prodCode unaryCode (prodCode (listCode Nat.bits) summaryCode)

def tableCode : Table → Word := prodCode unaryCode (prodCode (listCode Nat.bits) (listCode ratCode))

def preparedRow (n k den : ℕ) (entries : List (ℕ × ℕ)) (i : ℕ) : List ℚ :=
  ((List.range k).map (fun g => perturbedEntry (den, readCell (0, 0) entries (i * k + g)))) ++
    (List.range n).map (fun j => if i = j then 1 / 4 else 0)

def prepareTable (p : Input) : Table :=
  let (n, kept, count, maxValue, entries) := p
  let k := kept.length
  let den := 2 ^ errorExponent (n, k, count, maxValue)
  (n, kept, (List.range n).flatMap (preparedRow n k den entries))

noncomputable def prepareTableProcedure : Procedure inputCode tableCode prepareTable := by
  let cellCode := prodCode Nat.bits unaryCode
  let rankedCells := listCode cellCode
  let context := prodCode unaryCode (prodCode unaryCode (prodCode Nat.bits rankedCells))
  let rowCode := prodCode unaryCode context
  let values := listCode ratCode
  let kDenEntries := prodCode unaryCode (prodCode Nat.bits rankedCells)
  let row := first unaryCode context
  let ctx := second unaryCode context
  let agents := (first unaryCode kDenEntries).comp ctx
  let retainedData := (second unaryCode kDenEntries).comp ctx
  let columns := (first unaryCode (prodCode Nat.bits rankedCells)).comp retainedData
  let denEntries := (second unaryCode (prodCode Nat.bits rankedCells)).comp retainedData
  let base := binaryMul.comp ((unaryToBits.comp row).pair (unaryToBits.comp columns))
  let colContext := prodCode Nat.bits (prodCode Nat.bits rankedCells)
  let col := unaryToBits.comp (first unaryCode colContext)
  let cellCtx := second unaryCode colContext
  let locate := binaryAdd.comp (((first Nat.bits (prodCode Nat.bits rankedCells)).comp cellCtx).pair col)
  let cellData := (second Nat.bits (prodCode Nat.bits rankedCells)).comp cellCtx
  let fieldDen := (first Nat.bits rankedCells).comp cellData
  let fieldRanks := (second Nat.bits rankedCells).comp cellData
  let lookup := (listGet cellCode (0, 0)).comp (locate.pair fieldRanks)
  let originalCell := perturbedEntryProcedure.comp (fieldDen.pair lookup)
  let original := tabulate (ea := colContext) (eb := ratCode)
    (f := fun p g => perturbedEntry (p.2.1, readCell (0, 0) p.2.2 (p.1 + g))) 0 originalCell
  let originals := original.comp (columns.pair (base.pair denEntries))
  let auxInput := prodCode unaryCode Nat.bits
  let cmp := Control.Native.natEqP.comp ((second unaryCode Nat.bits).pair
    (unaryToBits.comp (first unaryCode Nat.bits)))
  let value : Procedure auxInput ratCode (fun p => if p.2 = p.1 then 1 / 4 else 0) :=
    (conditional cmp (constant auxInput ratCode (1 / 4 : ℚ)) (constant auxInput ratCode 0)).congrFun (by
      intro p
      simp)
  let auxiliary := tabulate (ea := Nat.bits) (eb := ratCode)
    (f := fun i j => if i = j then 1 / 4 else 0) 0 value
  let auxiliaries := auxiliary.comp (agents.pair (unaryToBits.comp row))
  let oneRow : Procedure rowCode values
      (fun p => preparedRow p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 p.1) :=
    ((Procedure.listAppend (ea := ratCode) 0).comp (originals.pair auxiliaries)).congrFun (by intro p; rfl)
  let rows := tabulate (ea := context) (eb := values)
    (f := fun p => preparedRow p.1 p.2.1 p.2.2.1 p.2.2.2) [] oneRow
  let keyCode := listCode Nat.bits
  let payload := prodCode keyCode summaryCode
  let n := first unaryCode payload
  let fields := second unaryCode payload
  let keys := (first keyCode summaryCode).comp fields
  let summary := (second keyCode summaryCode).comp fields
  let k := (Control.Native.rowSizeP Nat.bits 0).comp keys
  let count := (first unaryCode (prodCode Nat.bits rankedCells)).comp summary
  let data := (second unaryCode (prodCode Nat.bits rankedCells)).comp summary
  let vMax := (first Nat.bits rankedCells).comp data
  let ranks := (second Nat.bits rankedCells).comp data
  let exponent := errorExponentProcedure.comp (n.pair (k.pair (count.pair vMax)))
  let denominator := powTwo.comp exponent
  let generated := rows.comp (n.pair (n.pair (k.pair (denominator.pair ranks))))
  let flat := (Learning.GenerationCost.flattenP ratCode 0).comp generated
  have flattened (f : ℕ → List ℚ) (xs : List ℕ) : (xs.map f).flatten = xs.flatMap f := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, ih]
  exact (n.pair (keys.pair flat)).congrFun (by
    rintro ⟨n, ks, count, v, entries⟩
    simp [Function.comp_apply, prepareTable, flattened])

def encodeTable (p : Table) : Word :=
  let (n, kept, values) := p
  let m := kept.length + n
  encodeNat n ++ encodeNat m ++
    (List.range n).flatMap encodeNat ++ (List.range m).flatMap encodeNat ++
    values.flatMap encodeRat ++ encodeNat kept.length ++ kept.flatMap encodeNat

noncomputable def encodeTableProcedure : Procedure tableCode id encodeTable := by
  let keys := listCode Nat.bits
  let values := listCode ratCode
  let payload := prodCode keys values
  let agents := first unaryCode payload
  let fields := second unaryCode payload
  let kept := (first keys values).comp fields
  let rationals := (second keys values).comp fields
  let count := (Control.Native.rowSizeP Nat.bits 0).comp kept
  let goods := unaryAdd.comp (count.pair agents)
  let natList := Wire.flatten.comp (Procedure.listMap (0 : ℕ) ([] : Word) Wire.writeNat)
  let ratList := Wire.flatten.comp (Procedure.listMap (0 : ℚ) ([] : Word) Wire.writeRat)
  let writeNum := Wire.writeNat.comp unaryToBits
  let n := writeNum.comp agents
  let m := writeNum.comp goods
  let rows := natList.comp (Control.Native.addressRangeP.comp agents)
  let cols := natList.comp (Control.Native.addressRangeP.comp goods)
  let entries := ratList.comp rationals
  let k := writeNum.comp count
  let index := natList.comp kept
  let header := Procedure.append.comp (n.pair (Procedure.append.comp (m.pair rows)))
  let suffix := Procedure.append.comp (cols.pair (Procedure.append.comp (entries.pair
    (Procedure.append.comp (k.pair index)))))
  have flat_map {α : Type} (f : α → Word) (xs : List α) :
      (xs.map f).flatten = xs.flatMap f := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, ih]
  exact (Procedure.append.comp (header.pair suffix)).congrFun (by
    rintro ⟨n, ks, vs⟩
    simp [Function.comp_apply, encodeTable, flat_map, List.append_assoc])

private def rankEntries (start : ℕ) : List ℕ → List (ℕ × ℕ)
  | [] => []
  | v :: rest => (v, start + 1) :: rankEntries (if v = 0 then start else start + 1) rest

set_option maxHeartbeats 2000000 in
theorem summarize_scaled_agrees {I : Instance} (P : Preparation I) :
    let entries := (List.ofFn (fun i : I.Agent => List.ofFn (P.scaled i))).flatten
    let s := summarize entries
    s.1 = P.positiveEntries.card ∧ s.2.1 = P.maxValue ∧
      ∀ (i : I.Agent) (g : Fin P.keptCount), readCell (0, 0) s.2.2 (i.val * P.keptCount + g.val) =
        (P.scaled i g, P.entryIndex i g) := by
  classical
  let positive (x : ℕ) : Bool := decide (x ≠ 0)
  have fold_count (xs : List ℕ) (s : Summary) :
      (xs.foldl summaryStep s).1 = s.1 + (xs.filter positive).length := by
    induction xs generalizing s with
    | nil => simp
    | cons v vs ih =>
      simp only [List.foldl_cons, ih, summaryStep]
      by_cases hv : v = 0 <;> simp [positive, hv, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have fold_max (xs : List ℕ) (s : Summary) (b : ℕ) :
      (xs.foldl summaryStep s).2.1 ≤ b ↔ s.2.1 ≤ b ∧ ∀ x ∈ xs, x ≤ b := by
    induction xs generalizing s with
    | nil => simp
    | cons v vs ih =>
      simp [List.foldl_cons, ih, summaryStep, max_le_iff, List.mem_cons, forall_eq_or_imp, and_assoc]
  have ranks_append (xs : List ℕ) (s : Summary) :
      (xs.foldl summaryStep s).2.2.reverse = s.2.2.reverse ++ rankEntries s.1 xs := by
    induction xs generalizing s with
    | nil => simp [rankEntries]
    | cons v vs ih =>
      rw [List.foldl_cons, ih]
      simp [summaryStep, rankEntries, List.append_assoc]
  have ranks_get (xs : List ℕ) (start j : ℕ) (hj : j < xs.length) :
      (rankEntries start xs)[j]? = some (xs[j], start + ((xs.take j).filter positive).length + 1) := by
    induction xs generalizing start j with
    | nil => simp at hj
    | cons v vs ih =>
      cases j with
      | zero => simp [rankEntries]
      | succ j =>
        have hvlen : j < vs.length := by simpa using hj
        rw [rankEntries, List.getElem?_cons_succ, ih _ j hvlen]
        by_cases hv : v = 0 <;> simp [positive, hv, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  let e : P.Cell ≃ Fin (I.n * P.keptCount) := finProdFinEquiv
  let enumeration : List P.Cell := List.ofFn e.symm
  let scaled (c : P.Cell) : ℕ := P.scaled c.1 c.2
  let values : List ℕ := enumeration.map scaled
  have address (i : I.Agent) (g : Fin P.keptCount) : (e (i, g)).val = i.val * P.keptCount + g.val := by
    change g.val + P.keptCount * i.val = _
    ac_rfl
  have packed : (List.ofFn (fun i : I.Agent => List.ofFn (P.scaled i))).flatten = values := by
    unfold values enumeration
    rw [List.map_ofFn, List.ofFn_mul]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    apply congrArg List.ofFn
    funext g
    have inverse (z : Fin (I.n * P.keptCount)) (h : z.val = i.val * P.keptCount + g.val) :
        e.symm z = (i, g) := by
      apply e.injective
      rw [Equiv.apply_symm_apply]
      exact Fin.ext (h.trans (address i g).symm)
    exact (congrArg scaled (inverse _ (by simp))).symm
  have enumLen : enumeration.length = I.n * P.keptCount := by simp [enumeration]
  have enumAt (c : P.Cell) (hj : (e c).val < enumeration.length) : enumeration[(e c).val] = c := by
    have eAt : (⟨(e c).val, (e c).isLt⟩ : Fin (I.n * P.keptCount)) = e c := Fin.ext rfl
    simpa only [enumeration, List.getElem_ofFn, eAt] using e.symm_apply_apply c
  have mem_prefix (c : P.Cell) (j : ℕ) : c ∈ enumeration.take j ↔ (e c).val < j := by
    constructor
    · intro hc
      obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hc
      have hSmall : k < j := by simp only [List.length_take] at hk; omega
      have hBound : k < I.n * P.keptCount := by
        simp only [List.length_take, enumLen] at hk
        omega
      have he : e.symm ⟨k, hBound⟩ = c := by
        simpa only [List.getElem_take, enumeration, List.getElem_ofFn] using heq
      have hh := congrArg Fin.val (e.apply_symm_apply ⟨k, hBound⟩).symm
      rw [he] at hh
      exact hh ▸ hSmall
    · intro hj
      have ht : (e c).val < (enumeration.take j).length := by
        rw [List.length_take, enumLen]
        exact lt_min hj (e c).isLt
      refine List.mem_iff_getElem.mpr ⟨(e c).val, ht, ?_⟩
      rw [List.getElem_take]
      exact enumAt c (by rw [enumLen]; exact (e c).isLt)
  have enumMem (c : P.Cell) : c ∈ enumeration := by
    exact List.mem_ofFn.mpr ⟨e c, e.symm_apply_apply c⟩
  have enumNodup : enumeration.Nodup := List.nodup_ofFn_ofInjective e.symm.injective
  have positive_iff (c : P.Cell) : positive (scaled c) = true ↔ c ∈ P.positiveEntries := by
    simp only [positive, decide_eq_true_eq, Preparation.positiveEntries, Finset.mem_filter,
      Finset.mem_univ, true_and]
    have hD : (0 : ℚ) < P.rowFactor c.1 := by exact_mod_cast P.rowFactor_pos c.1
    have hPos : 0 < scaled c ↔ 0 < I.v c.1 (P.keptGood c.2) := by
      have hCast : (0 : ℚ) < (scaled c : ℚ) ↔ 0 < scaled c := Nat.cast_pos
      rw [← hCast]
      change (0 : ℚ) < (P.scaled c.1 c.2 : ℚ) ↔ _
      rw [P.scaled_eq_rowFactor_mul]
      exact ⟨fun h => pos_of_mul_pos_right h hD.le, fun h => mul_pos hD h⟩
    exact Nat.pos_iff_ne_zero.symm.trans hPos
  have length_filter_map (xs : List P.Cell) :
      ((xs.map scaled).filter positive).length = (xs.filter (fun c => positive (scaled c))).length := by
    induction xs with
    | nil => rfl
    | cons c xs ih =>
      by_cases h : positive (scaled c) = true <;> simp [h, ih]
  have count_prefix (j : ℕ) : ((values.take j).filter positive).length =
      (P.positiveEntries.filter (fun c => (e c).val < j)).card := by
    rw [show values.take j = (enumeration.take j).map scaled from List.map_take.symm,
      length_filter_map]
    let passing := (enumeration.take j).filter (fun c => positive (scaled c))
    have hn : passing.Nodup := List.Nodup.filter _ (enumNodup.sublist (List.take_sublist _ _))
    change passing.length = _
    rw [← List.toFinset_card_of_nodup hn]
    congr 1
    ext c
    simp only [passing, List.mem_toFinset, List.mem_filter, mem_prefix, positive_iff, Finset.mem_filter]
    exact and_comm
  have full_count : (values.filter positive).length = P.positiveEntries.card := by
    have filter_all : (P.positiveEntries.filter fun c => (e c).val < values.length) = P.positiveEntries := by
      ext c
      have hc : (e c).val < values.length := by
        simpa only [values, List.length_map, enumLen] using (e c).isLt
      simp [hc]
    simpa only [List.take_length, filter_all] using count_prefix values.length
  have row_before {i j : I.Agent} (g g' : Fin P.keptCount) (hi : i < j) :
      (e (i, g)).val < (e (j, g')).val := by
    rw [address, address]
    have hMul := Nat.mul_le_mul_right P.keptCount (Nat.succ_le_of_lt hi)
    change (i.val + 1) * P.keptCount ≤ j.val * P.keptCount at hMul
    rw [Nat.add_mul, Nat.one_mul] at hMul
    have hg := g.isLt
    omega
  have index_before (i : I.Agent) (g : Fin P.keptCount) (c : P.Cell) :
      (e c).val < (e (i, g)).val ↔ c.1 < i ∨ (c.1 = i ∧ c.2 < g) := by
    rcases c with ⟨a, b⟩
    rcases lt_trichotomy a i with hlt | rfl | hgt
    · exact ⟨fun _ => Or.inl hlt, fun _ => row_before b g hlt⟩
    · rw [address, address, Nat.add_lt_add_iff_left]
      simp
    · exact ⟨fun h => False.elim ((not_lt_of_gt (row_before g b hgt)) h), fun h => by
        rcases h with h | ⟨h, _⟩
        · exact False.elim ((not_lt_of_gt hgt) h)
        · exact False.elim (hgt.ne' h)⟩
  have rank_count (i : I.Agent) (g : Fin P.keptCount) :
      ((values.take (e (i, g)).val).filter positive).length + 1 = P.entryIndex i g := by
    rw [count_prefix, Preparation.entryIndex, Nat.add_comm]
    congr 2
    ext c
    simp only [Finset.mem_filter, index_before]
  let initial : Summary := (0, 1, [])
  let state := values.foldl summaryStep initial
  have below_max (c : P.Cell) : scaled c ≤ P.maxValue := by
    by_cases hp : c ∈ P.positiveEntries
    · exact (Finset.le_sup (f := scaled) hp).trans (le_max_right _ _)
    · have hz : scaled c = 0 := by
        by_contra hn
        exact hp ((positive_iff c).mp (by simp [positive, hn]))
      simpa only [hz] using Nat.zero_le P.maxValue
  have max_exact : state.2.1 = P.maxValue := by
    apply le_antisymm
    · refine (fold_max values initial P.maxValue).mpr ⟨le_max_left _ _, ?_⟩
      intro x hx
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
      exact below_max c
    · have hMax := (fold_max values initial state.2.1).mp le_rfl
      refine max_le hMax.1 (Finset.sup_le fun c _ => ?_)
      exact hMax.2 _ (List.mem_map.mpr ⟨c, enumMem c, rfl⟩)
  change (summarize _).1 = P.positiveEntries.card ∧ _
  rw [packed]
  refine ⟨?_, max_exact, ?_⟩
  · change state.1 = _
    unfold state
    rw [fold_count]
    exact (Nat.zero_add _).trans full_count
  · intro i g
    rw [← address i g]
    have hLen : (e (i, g)).val < values.length := by
      simpa only [values, List.length_map, enumLen] using (e (i, g)).isLt
    have hv : values[(e (i, g)).val] = P.scaled i g := by
      change (enumeration.map scaled)[_] = _
      rw [List.getElem_map]
      exact congrArg scaled (enumAt (i, g) _)
    change readCell (0, 0) (values.foldl summaryStep initial).2.2.reverse (e (i, g)).val = _
    rw [ranks_append]
    simp only [initial, List.reverse_nil, List.nil_append]
    rw [readCell, List.headD_eq_head?_getD, List.head?_drop, ranks_get _ _ _ hLen,
      Option.getD_some, Nat.zero_add, rank_count, hv]

theorem encode_prepared_agrees {I : Instance} (P : Preparation I) (h : P.IsPreparation) :
    let kept := List.ofFn (fun g => (P.keptGood g).val)
    let entries := (List.ofFn (fun i : I.Agent => List.ofFn (P.scaled i))).flatten
    encodeTable (prepareTable (I.n, kept, summarize entries)) =
      encodeInstance P.prepared ++ encodeNat P.keptCount ++ kept.flatMap encodeNat := by
  let kept := List.ofFn (fun g => (P.keptGood g).val)
  let entries := (List.ofFn (fun i : I.Agent => List.ofFn (P.scaled i))).flatten
  let s := summarize entries
  obtain ⟨hCount, hMax, hRanks⟩ := summarize_scaled_agrees P
  have hLength : kept.length = P.keptCount := by simp [kept]
  have hExponent : errorExponent (I.n, kept.length, s.1, s.2.1) = P.perturbationExponent := by
    change s.1 = P.positiveEntries.card at hCount
    change s.2.1 = P.maxValue at hMax
    rw [hLength, hCount, hMax]
    rfl
  have scalar_agrees (a r : ℕ) : perturbedEntry (2 ^ P.perturbationExponent, (a, r)) =
      (a : ℚ) * (1 + 2 ^ r * P.perturbation) := by
    rw [perturbedEntry, Rat.mkRat_eq_div]
    push_cast
    rw [Preparation.perturbation, div_pow, one_pow]
    have hd : (2 : ℚ) ^ P.perturbationExponent ≠ 0 := by positivity
    field_simp [hd] <;> ring
  have row_agrees (i : I.Agent) :
      preparedRow I.n P.keptCount (2 ^ P.perturbationExponent) s.2.2 i.val =
        List.ofFn (P.v i) := by
    rw [List.ofFn_add]
    unfold preparedRow
    congr 1
    · apply List.ext_getElem
      · simp
      · intro k _ hk
        let g : Fin P.keptCount := ⟨k, by simpa only [List.length_ofFn] using hk⟩
        simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
        change perturbedEntry (2 ^ P.perturbationExponent,
          readCell (0, 0) s.2.2 (i.val * P.keptCount + g.val)) = P.v i (P.originalColumn g)
        rw [hRanks i g, h.2.2.1 i g]
        exact scalar_agrees (P.scaled i g) (P.entryIndex i g)
    · apply List.ext_getElem
      · simp
      · intro k _ hk
        let j : I.Agent := ⟨k, by simpa only [List.length_ofFn] using hk⟩
        simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
        change (if i.val = j.val then (1 / 4 : ℚ) else 0) = P.v i (P.auxiliaryColumn j)
        rw [h.2.2.2 i j]
        simp only [Fin.val_inj]
  let row := preparedRow I.n P.keptCount (2 ^ P.perturbationExponent) s.2.2
  have table_agrees : (List.range I.n).map row = List.ofFn (fun i : I.Agent => List.ofFn (P.v i)) := by
    apply List.ext_getElem
    · simp
    · intro k _ hk
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
      exact row_agrees ⟨k, by simpa only [List.length_ofFn] using hk⟩
  have flatten (xs : List ℕ) : xs.flatMap row = (xs.map row).flatten := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.flatMap_cons, List.map_cons, List.flatten_cons, ih]
  have labels (k : ℕ) : (List.ofFn (fun j : Fin k => j.val)) = List.range k := by
    apply List.ext_getElem <;> simp
  change encodeTable (I.n, kept, (List.range I.n).flatMap
    (preparedRow I.n kept.length (2 ^ errorExponent (I.n, kept.length, s.1, s.2.1)) s.2.2)) =
      encodeInstance P.prepared ++ encodeNat P.keptCount ++ kept.flatMap encodeNat
  rw [hExponent, hLength]
  change encodeTable (I.n, kept, (List.range I.n).flatMap row) = _
  rw [flatten, table_agrees]
  simp [encodeTable, encodeInstance, Preparation.prepared, hLength, labels, List.append_assoc]

end EF1FPO.PreparationOutputWire
