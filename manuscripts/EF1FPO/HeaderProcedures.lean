import EF1FPO.PricePacketProcedures

/-! Count-field parsing for the public contraction packets. -/

set_option autoImplicit false

namespace EF1FPO.PricePacketProcedures

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec

def rawNatField (n : ℕ × Word) : Word := encodeNat n.1 ++ n.2

def rawUnaryField (n : ℕ × Word) : Word := List.replicate n.1 true ++ false :: n.2

/-- Apply a procedure to the suffix left by a previous parse. -/
noncomputable def readSuffix {X Y : Type} {input suffix : X → Word}
    {encoding : Y → Word} {read : X → Y}
    (readPrefix : Procedure input id suffix) (next : Procedure suffix encoding read) :
    Procedure input encoding read :=
  (next.comp (readPrefix.result (ec := suffix) (h := id) (by intro x; rfl))).congrFun
    (by intro x; rfl)

noncomputable def decodeNatField : Procedure rawNatField (prodCode Nat.bits id) id :=
  (identity (prodCode Nat.bits id)).congrEncoding
    (by intro n; simp [rawNatField, prodCode, pairBits, encodeNat, quoteBits_eq_frame])
    (by intro n; rfl)

private def unaryStore (suffix count active : Word) : Store (Fin 3) := ![suffix, count, active]

@[simp] private theorem unaryStore_zero (p c a : Word) : unaryStore p c a 0 = p := rfl
@[simp] private theorem unaryStore_one (p c a : Word) : unaryStore p c a 1 = c := rfl
@[simp] private theorem unaryStore_two (p c a : Word) : unaryStore p c a 2 = a := rfl

@[simp] private theorem unaryStore_update_zero (p c a x : Word) :
    Function.update (unaryStore p c a) 0 x = unaryStore x c a := by
  funext i
  fin_cases i <;> simp

@[simp] private theorem unaryStore_update_one (p c a x : Word) :
    Function.update (unaryStore p c a) 1 x = unaryStore p x a := by
  funext i
  fin_cases i <;> simp

@[simp] private theorem unaryStore_update_two (p c a x : Word) :
    Function.update (unaryStore p c a) 2 x = unaryStore p c x := by
  funext i
  fin_cases i <;> simp

private def walkUnaryStep : Program (Fin 3) :=
  .cases 0 .skip .skip (.seq (.push 1 true) (.push 2 true))

private def walkUnary : Program (Fin 3) := .loop 2 walkUnaryStep walkUnaryStep

noncomputable def decodeUnaryField : Procedure rawUnaryField (prodCode unaryCode id) id where
  K := Fin 3
  finiteK := inferInstance
  decideK := inferInstance
  input := 0
  output := 0
  program := .seq (.push 2 true) (.seq walkUnary (quoteMove 1 0 2))
  bound := Polynomial.C 11 * Polynomial.X + Polynomial.C 10
  runs pair := by
    obtain ⟨n, suffix⟩ := pair
    have scan (count acc : ℕ) :
        Runs walkUnary (unaryStore (rawUnaryField (count, suffix)) (List.replicate acc true) [true])
          (unaryStore suffix (List.replicate (count + acc) true) []) (4 * count + 4) := by
      induction count generalizing acc with
      | zero =>
        have read : Runs walkUnaryStep (unaryStore (false :: suffix) (List.replicate acc true) [])
            (unaryStore suffix (List.replicate acc true) []) 2 := by
          unfold walkUnaryStep
          apply Runs.cases_false (xs := suffix)
          · rfl
          · simp only [unaryStore_update_zero]
            exact Runs.skip _
        have done : Runs walkUnary (unaryStore suffix (List.replicate acc true) [])
            (unaryStore suffix (List.replicate acc true) []) 1 := Runs.loop_nil rfl
        have step := Runs.loop_true (s := unaryStore (false :: suffix) (List.replicate acc true) [true])
          (xs := []) rfl (by simpa only [unaryStore_update_two] using read) done
        simpa only [walkUnary, rawUnaryField, List.replicate_zero, List.nil_append, Nat.zero_add,
          Nat.mul_zero, show (1 : ℕ) + 2 + 1 = 4 by decide]
          using step
      | succ count ih =>
        let remaining := rawUnaryField (count, suffix)
        have collect : Runs (.push 1 true) (unaryStore remaining (List.replicate acc true) [])
            (unaryStore remaining (List.replicate (acc + 1) true) []) 1 := by
          simpa only [unaryStore_one, unaryStore_update_one, List.replicate_succ] using
            Runs.push (unaryStore remaining (List.replicate acc true) []) 1 true
        have continueScan : Runs (.push 2 true) (unaryStore remaining (List.replicate (acc + 1) true) [])
            (unaryStore remaining (List.replicate (acc + 1) true) [true]) 1 := by
          simpa only [unaryStore_two, unaryStore_update_two] using
            Runs.push (unaryStore remaining (List.replicate (acc + 1) true) []) 2 true
        have read : Runs walkUnaryStep (unaryStore (true :: remaining) (List.replicate acc true) [])
            (unaryStore remaining (List.replicate (acc + 1) true) [true]) 3 := by
          unfold walkUnaryStep
          apply Runs.cases_true (xs := remaining)
          · rfl
          · simp only [unaryStore_update_zero]
            exact Runs.seq collect continueScan
        have step := Runs.loop_true (s := unaryStore (true :: remaining) (List.replicate acc true) [true])
          (xs := []) rfl (by simpa only [unaryStore_update_two] using read) (ih (acc + 1))
        rw [show count + (acc + 1) = count.succ + acc by omega] at step
        rw [show (4 * count + 4) + 3 + 1 = 4 * count.succ + 4 by omega] at step
        simpa only [walkUnary, remaining, rawUnaryField, List.replicate_succ, List.cons_append,
          Nat.succ_eq_add_one] using step
    let raw := rawUnaryField (n, suffix)
    let inputStore := singletonStore (0 : Fin 3) raw
    have start : Runs (.push 2 true) inputStore (unaryStore raw [] [true]) 1 := by
      convert Runs.push inputStore 2 true using 1
      funext i
      fin_cases i <;> simp [inputStore, singletonStore]
    have read := scan n 0
    simp only [List.replicate_zero, Nat.add_zero] at read
    let readStore := unaryStore suffix (List.replicate n true) []
    have write : Runs (quoteMove (1 : Fin 3) 0 2) readStore
        (singletonStore 0 (prodCode unaryCode id (n, suffix))) (7 * n + 5) := by
      have run := quoteMove_runs (1 : Fin 3) 0 2 (by decide) (by decide) (by decide) readStore rfl
      simp only [readStore, unaryStore_zero, unaryStore_one, unaryStore_update_one,
        unaryStore_update_zero, List.length_replicate] at run
      convert run using 1
      funext i
      fin_cases i <;> simp [singletonStore, prodCode, pairBits, unaryCode]
    refine ⟨(7 * n + 5) + (4 * n + 4) + 1, ?_, Runs.seq start (Runs.seq read write)⟩
    simp [Polynomial.eval_add, Polynomial.eval_mul, rawUnaryField] <;> omega

end EF1FPO.PricePacketProcedures
