import EF1FPO.Preparation
import OAI.Computability.QuantumFactoring.BitStackTabulate
import OAI.Optimization.LinearProgramming.PriceGame.MarketInputsMachine
import OAI.Optimization.LinearProgramming.PriceGame.MarketContextMap
import OAI.Optimization.LinearProgramming.PriceGame.ControlScalarMachine

/-! Binary arithmetic used to construct the perturbed instance. -/

set_option autoImplicit false

namespace EF1FPO.PreparationArithmeticWire

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.PriceGame.Market

/-- Scale a packed row by the product of its denominators. -/
def scaleRow (values : List ℚ) : List ℕ :=
  let denominator := values.foldl (fun a q => a * q.den) 1
  values.map (Denominator.qty denominator)

noncomputable def scaleRowProcedure : Procedure (listCode ratCode) (listCode Nat.bits) scaleRow := by
  let rowCode := listCode ratCode
  let input := (identity rowCode).pair InputMachine.denominatorP
  exact ((GridMachine.mapWithContext (0 : ℚ) (0 : ℕ) InputMachine.qtyP).comp input).congrFun
    (by intro row; rfl)

theorem scaleRow_retained_entry {I : Instance} (P : Preparation I) (i : I.Agent)
    (g : Fin P.keptCount) :
    (scaleRow (List.ofFn (I.v i)))[(P.keptGood g).val]? = some (P.scaled i g) := by
  let values := List.ofFn (I.v i)
  let q := I.v i (P.keptGood g)
  have hDen : values.foldl (fun a q => a * q.den) 1 = P.rowFactor i := by
    simpa only [values, List.ofFn_eq_map, Preparation.rowFactor, Denominator.denominator] using
      InputMachine.denominatorP_agrees (I.v i)
  have hd : q.den ∣ P.rowFactor i :=
    Denominator.den_dvd_denominator (I.v i) (P.keptGood g)
  have hScaled : Denominator.qty (P.rowFactor i) q = P.scaled i g := by
    have hCast : (Denominator.qty (P.rowFactor i) q : ℚ) = (P.scaled i g : ℚ) :=
      (Denominator.cast_qty (I.nonneg i (P.keptGood g)) hd).trans (P.scaled_eq_rowFactor_mul i g).symm
    exact_mod_cast hCast
  have hLen : (P.keptGood g).val < values.length := by
    simpa only [values, List.length_ofFn] using (P.keptGood g).isLt
  have hValue : values[(P.keptGood g).val]? = some q := by
    rw [List.getElem?_eq_getElem hLen]
    simp only [values, q, List.getElem_ofFn]
  change (values.map (Denominator.qty (values.foldl (fun a q => a * q.den) 1)))[_]? = _
  simp only [List.getElem?_map, hDen, hValue, Option.map_some, hScaled]

/-- The exponent is supplied in unary, so the output width is bounded by the input width product. -/
noncomputable def powNatural : Procedure (prodCode unaryCode Nat.bits) Nat.bits
    (fun p : ℕ × ℕ => p.2 ^ p.1) := by
  let code := prodCode Nat.bits Nat.bits
  let update (x : ℕ × ℕ) := (x.1, x.2 * x.1)
  let multiply := binaryMul.comp (swap Nat.bits Nat.bits)
  let step : Procedure code code update := ((first Nat.bits Nat.bits).pair multiply).congrFun (by
    intro x
    rfl)
  have iters (n : ℕ) (x : ℕ × ℕ) : (update^[n]) x = (x.1, x.2 * x.1 ^ n) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih]; simp [update, pow_succ, mul_assoc]
  have growth (base start n : ℕ) : (start * base ^ n).bits.length ≤
      start.bits.length + n * base.bits.length := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← mul_assoc]
      exact (bits_length_mul _ _).trans ((Nat.add_le_add_right ih _).trans_eq (by ring))
  let width : Polynomial ℕ := Polynomial.X^2 + Polynomial.X
  let run := step.iterate width (by
    intro n x i hi
    rw [iters]
    let L := n + (code x).length
    have hBase : x.1.bits.length ≤ L := by
      simp only [L, code, prodCode, pairBits_length]
      omega
    have hMul : i * x.1.bits.length ≤ L^2 := by
      rw [pow_two]
      exact Nat.mul_le_mul (hi.trans (Nat.le_add_right _ _)) hBase
    have hRest : 2 * x.1.bits.length + x.2.bits.length + 1 ≤ L := by
      simp only [L, code, prodCode, pairBits_length]
      omega
    have hGrow := growth x.1 x.2 i
    change (code (x.1, x.2 * x.1 ^ i)).length ≤ width.eval L
    simp only [code, prodCode, pairBits_length, width, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X]
    omega)
  let n := first unaryCode Nat.bits
  let a := second unaryCode Nat.bits
  let init := a.pair (constant (prodCode unaryCode Nat.bits) Nat.bits 1)
  exact ((second Nat.bits Nat.bits).comp (run.comp (n.pair init))).congrFun (by
    rintro ⟨n, a⟩
    change ((update^[n]) (a, 1)).2 = _
    simp [iters])

abbrev Summary := ℕ × ℕ × List (ℕ × ℕ)

def summaryCode : Summary → List Bool :=
  prodCode unaryCode (prodCode Nat.bits (listCode (prodCode Nat.bits unaryCode)))

def summaryStep (s : Summary) (v : ℕ) : Summary :=
  (if v = 0 then s.1 else s.1 + 1, max s.2.1 v, (v, s.1 + 1) :: s.2.2)

def summarize (values : List ℕ) : Summary :=
  let s := values.foldl summaryStep (0, 1, [])
  (s.1, s.2.1, s.2.2.reverse)

noncomputable def summarizeProcedure : Procedure (listCode Nat.bits) summaryCode summarize := by
  let inputCode := listCode Nat.bits
  let cellCode := prodCode Nat.bits unaryCode
  let cellsCode := listCode cellCode
  let payload := prodCode Nat.bits cellsCode
  let stepCode := prodCode Nat.bits summaryCode
  let value := first Nat.bits summaryCode
  let state := second Nat.bits summaryCode
  let count := (first unaryCode payload).comp state
  let data := (second unaryCode payload).comp state
  let largest := (first Nat.bits cellsCode).comp data
  let previous := (second Nat.bits cellsCode).comp data
  let isZero := OAI.Optimization.LinearProgramming.PriceGame.Control.Native.natEqP.comp
    (value.pair (constant stepCode Nat.bits 0))
  let countUp := unarySuccessor.comp count
  let countNew := conditional isZero count countUp
  let larger := conditional (binaryLe.comp (value.pair largest)) largest value
  let cell := value.pair countUp
  let entries := (listCons cellCode).comp (cell.pair previous)
  let step : Procedure stepCode summaryCode (fun p => summaryStep p.2 p.1) :=
    (countNew.pair (larger.pair entries)).congrFun (by
      rintro ⟨v, k, m, cs⟩
      change (ite (decide (v = 0) = true) k (k + 1),
        ite (decide (v ≤ m) = true) m v, (v, k + 1) :: cs) = summaryStep (k, m, cs) v
      by_cases h : v ≤ m
      · simp [summaryStep, h, max_eq_left h]
      · simp [summaryStep, h, max_eq_right (le_of_not_ge h)])
  have running_width (xs : List ℕ) (s : Summary) (B T : ℕ)
      (hCount : s.1 + xs.length ≤ T) (hMax : s.2.1.bits.length ≤ B)
      (hValues : ∀ v ∈ xs, v.bits.length ≤ B) :
      let out := xs.foldl summaryStep s
      out.1 ≤ s.1 + xs.length ∧ out.2.1.bits.length ≤ B ∧
      (cellsCode out.2.2).length ≤ (cellsCode s.2.2).length + xs.length * (4 * B + 2 * T + 4) := by
    induction xs generalizing s with
    | nil => simpa using hMax
    | cons v xs ih =>
      let next := summaryStep s v
      have hV := hValues v List.mem_cons_self
      have hStep : next.1 ≤ s.1 + 1 := by
        change (if v = 0 then s.1 else s.1 + 1) ≤ s.1 + 1
        split <;> omega
      have hNewMax : next.2.1.bits.length ≤ B := by
        change (max s.2.1 v).bits.length ≤ B
        rcases le_total s.2.1 v with h | h
        · rwa [max_eq_right h]
        · rwa [max_eq_left h]
      have hNewCount : next.1 + xs.length ≤ T := by
        rw [List.length_cons] at hCount
        omega
      have hEntry : (cellsCode next.2.2).length ≤
          (cellsCode s.2.2).length + (4 * B + 2 * T + 4) := by
        rw [List.length_cons] at hCount
        simp only [next, summaryStep, cellsCode, cellCode, listCode_length_cons, prodCode,
          pairBits_length, unaryCode, List.length_replicate]
        omega
      obtain ⟨hc, hm, hs⟩ := ih next hNewCount hNewMax
        (fun v hv => hValues v (List.mem_cons_of_mem _ hv))
      change (xs.foldl summaryStep next).1 ≤ s.1 + (v :: xs).length ∧
        (xs.foldl summaryStep next).2.1.bits.length ≤ B ∧ _
      refine ⟨by simp only [List.length_cons]; omega, hm, ?_⟩
      simp only [List.foldl_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      change (cellsCode (xs.foldl summaryStep next).2.2).length ≤ _
      omega
  let width : Polynomial ℕ := Polynomial.C 16 * (Polynomial.X + 1)^2
  let scan := foldList 0 step width (by
    intro xs s i
    let L := (listCode Nat.bits xs).length + (summaryCode s).length
    change (summaryCode ((xs.take i).foldl summaryStep s)).length ≤ width.eval L
    have hParts : s.1 ≤ (summaryCode s).length ∧
        s.2.1.bits.length ≤ (summaryCode s).length ∧ (cellsCode s.2.2).length ≤ (summaryCode s).length := by
      simp only [summaryCode, cellsCode, cellCode, prodCode, pairBits_length, unaryCode, List.length_replicate]
      omega
    have hLen : (xs.take i).length ≤ (listCode Nat.bits xs).length := by
      have h := list_length_le_code Nat.bits xs
      simp only [List.length_take]
      exact (Nat.min_le_right _ _).trans h
    have hCount : s.1 + (xs.take i).length ≤ L := by
      unfold L
      omega
    have hMax : s.2.1.bits.length ≤ L := hParts.2.1.trans (Nat.le_add_left _ _)
    have hValues (v : ℕ) (hv : v ∈ xs.take i) : v.bits.length ≤ L :=
      (code_le_of_mem Nat.bits (List.mem_of_mem_take hv)).trans (Nat.le_add_right _ _)
    obtain ⟨ha, hb, hc⟩ := running_width (xs.take i) s L L hCount hMax hValues
    have hTake : (xs.take i).length ≤ L := hLen.trans (Nat.le_add_right _ _)
    have hCons := Nat.mul_le_mul_right (4 * L + 2 * L + 4) hTake
    have hInit : (cellsCode s.2.2).length ≤ L := hParts.2.2.trans (Nat.le_add_left _ _)
    let out := (xs.take i).foldl summaryStep s
    have hBytes : (summaryCode out).length =
        2 * out.1 + 2 * out.2.1.bits.length + (cellsCode out.2.2).length + 2 := by
      simp only [summaryCode, cellsCode, cellCode, prodCode, pairBits_length, unaryCode, List.length_replicate]
      omega
    change (summaryCode out).length ≤ width.eval L
    rw [hBytes]
    simp only [width, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    change out.1 ≤ _ at ha
    change out.2.1.bits.length ≤ _ at hb
    change (cellsCode out.2.2).length ≤ _ at hc
    nlinarith)
  let start := (identity inputCode).pair (constant inputCode summaryCode (0, 1, []))
  let fold := scan.comp start
  let reverse := (listReverse cellCode (0, 0)).comp (second Nat.bits cellsCode)
  let restore := (first unaryCode payload).pair
    (((first Nat.bits cellsCode).pair reverse).comp (second unaryCode payload))
  exact (restore.comp fold).congrFun (by intro vals; rfl)

end EF1FPO.PreparationArithmeticWire
