import EF1FPO.PricePacketProcedures
import OAI.Computability.QuantumFactoring.BitStackListOps
import OAI.Computability.QuantumFactoring.BitStackSums
import OAI.Optimization.LinearProgramming.OracleSpec.PriceEncoding

/-! A decoder for a dimension-delimited list of rational fields. -/

set_option autoImplicit false

namespace EF1FPO.PricePacketProcedures

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec

def rawRatList (values : List ℚ) : Word := values.flatMap encodeRat

def countedRatList (values : List ℚ) : Word :=
  prodCode unaryCode id (values.length, rawRatList values)

abbrev RatListReader := List ℚ × List ℚ

def ratListReaderCode : RatListReader → Word := prodCode rawRatList (listCode ratCode)

def readNextRat : RatListReader → RatListReader
  | ([], read) => ([], read)
  | (q :: rest, read) => (rest, read ++ [q])

theorem readNextRat_width (start : RatListReader) (j : ℕ) :
    (ratListReaderCode ((readNextRat^[j]) start)).length ≤
      8 * ((ratListReaderCode start).length + 1) := by
  have hField (q : ℚ) : (encodeRat q).length ≤ 2 * (ratCode q).length + 2 ∧
      2 * (ratCode q).length + 2 ≤ 6 * (encodeRat q).length := by
    simp only [encodeRat, encodeNat, frame_length, List.length_cons, List.length_append,
      ratCode, intCode, intData, prodCode, pairBits_length, boolCode, List.length_nil]
    omega
  have hList (xs : List ℚ) : (rawRatList xs).length ≤ (listCode ratCode xs).length ∧
      (listCode ratCode xs).length ≤ 6 * (rawRatList xs).length + 1 := by
    induction xs with
    | nil => simp [rawRatList, listCode]
    | cons q rest ih =>
      have h := hField q
      simp only [rawRatList, List.flatMap_cons, List.length_append, listCode_length_cons] at ih ⊢
      omega
  let total (s : RatListReader) := (rawRatList s.1).length + (rawRatList s.2).length
  have hStep (s : RatListReader) : total (readNextRat s) = total s := by
    rcases s with ⟨rest, seen⟩
    cases rest with
    | nil => rfl
    | cons q rest =>
      simp [total, readNextRat, rawRatList,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hInvariant : total ((readNextRat^[j]) start) = total start := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', hStep, ih]
  have hLen (s : RatListReader) : (ratListReaderCode s).length =
      2 * (rawRatList s.1).length + 1 + (listCode ratCode s.2).length := by
    simp only [ratListReaderCode, prodCode, pairBits_length]
    omega
  have hStart : total start ≤ (ratListReaderCode start).length := by
    rw [hLen]
    have h := (hList start.2).1
    dsimp only [total]
    omega
  let state := (readNextRat^[j]) start
  have hWidth : (ratListReaderCode state).length ≤ 6 * total state + 2 := by
    rw [hLen]
    have h := (hList state.2).2
    dsimp only [total]
    omega
  change (ratListReaderCode state).length ≤ _
  change total state = total start at hInvariant
  omega

theorem readNextRat_finishes (values : List ℚ) :
    (readNextRat^[values.length]) (values, []) = ([], values) := by
  have hGeneral (rest seen : List ℚ) :
      (readNextRat^[rest.length]) (rest, seen) = ([], seen ++ rest) := by
    induction rest generalizing seen with
    | nil => simp
    | cons q rest ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (readNextRat^[rest.length]) (rest, seen ++ [q]) = _
      rw [ih]
      simp
  simpa using hGeneral values []

noncomputable def readNextRatProc : Procedure ratListReaderCode ratListReaderCode readNextRat := by
  let seenCode := listCode ratCode
  let tokenCode : ℚ × List ℚ → Word := fun p => rawRatField (p.1, rawRatList p.2)
  let moreCode := prodCode tokenCode seenCode
  let unitCode := prodCode ratCode rawRatList
  let token : Procedure tokenCode unitCode id :=
    (decodeRatField.precompose (fun p : ℚ × List ℚ => (p.1, rawRatList p.2))).result
      (by intro p; rfl)
  let parsed := token.left seenCode
  let pair := (first unitCode seenCode).comp parsed
  let remaining := (second ratCode rawRatList).comp pair
  let value := (first ratCode rawRatList).comp pair
  let accumulated := (second unitCode seenCode).comp parsed
  let singleton := (Procedure.listCons (ea := ratCode)).comp
    (value.pair (constant moreCode seenCode ([] : List ℚ)))
  let appendValue := (Procedure.listAppend (ea := ratCode) (0 : ℚ)).comp
    (accumulated.pair singleton)
  let more := remaining.pair appendValue
  let raw : Procedure ratListReaderCode id (fun p => rawRatList p.1) :=
    (first rawRatList seenCode).result (by intro p; rfl)
  let nonempty : Procedure ratListReaderCode id (fun p => [!(rawRatList p.1).isEmpty]) :=
    (boolNot.comp (Procedure.isEmpty.comp raw)).result (by intro p; rfl)
  let full : Procedure ratListReaderCode id ratListReaderCode :=
    (identity ratListReaderCode).result (by intro p; rfl)
  let marked : Procedure ratListReaderCode (sumCode ratListReaderCode moreCode)
      (fun p => match p.1 with | [] => .inl p | q :: rest => .inr ((q, rest), p.2)) :=
    (Procedure.append.comp (nonempty.pair full)).result (by
      rintro ⟨rest, seen⟩
      cases rest with
      | nil => rfl
      | cons q rest =>
        change [!(rawRatList (q :: rest)).isEmpty] ++ ratListReaderCode (q :: rest, seen) =
          true :: moreCode ((q, rest), seen)
        simp [rawRatList, encodeRat, ratListReaderCode, moreCode, tokenCode, rawRatField,
          prodCode, pairBits, seenCode, List.append_assoc])
  exact ((casesSum (identity ratListReaderCode) more).comp marked).congrFun (by
    rintro ⟨rest, seen⟩
    cases rest <;> rfl)

noncomputable def decodeRatList : Procedure countedRatList (listCode ratCode) id := by
  let fromInput (values : List ℚ) := (values.length, values)
  let count : Procedure countedRatList unaryCode List.length :=
    (first unaryCode rawRatList).precompose fromInput
  let fields : Procedure countedRatList rawRatList id :=
    (second unaryCode rawRatList).precompose fromInput
  let initial := fields.pair (constant countedRatList (listCode ratCode) ([] : List ℚ))
  let width : Polynomial ℕ := Polynomial.C 8 * (Polynomial.X + 1)
  let loop := readNextRatProc.iterate width (by
    intro n start i hi
    have hw := readNextRat_width start i
    simp only [width, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
    omega)
  let parsed := (second rawRatList (listCode ratCode)).comp (loop.comp (count.pair initial))
  exact parsed.congrFun (by
    intro values
    exact congrArg Prod.snd (readNextRat_finishes values))

end EF1FPO.PricePacketProcedures
