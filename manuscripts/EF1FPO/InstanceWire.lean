import EF1FPO.Computation
import EF1FPO.HeaderProcedures
import OAI.Computability.QuantumFactoring.BitStackListOps
import OAI.Optimization.LinearProgramming.OracleSpec.UnaryBootstrap

/-! Dimension-delimited instance prefixes on the binary stack machine. -/

set_option autoImplicit false

namespace EF1FPO.InstanceWire

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open EF1FPO.PricePacketProcedures (rawNatField decodeNatField)

abbrev BoundedNatField := { p : ℕ × Word // p.1 ≤ (rawNatField p).length }

def bootstrappedNatCode (p : ℕ × Word) : Word :=
  frame (unaryCode p.1) ++ rawNatField p

noncomputable def boundedNatField : Procedure (fun p : BoundedNatField => rawNatField p.val)
    bootstrappedNatCode Subtype.val where
  K := Fin 4
  finiteK := inferInstance
  decideK := inferInstance
  input := 0
  output := 0
  program := UnaryBootstrap.program
  bound := Polynomial.C 64 * (Polynomial.X + 1)^2
  runs p := by
    obtain ⟨steps, hsteps, hrun⟩ := UnaryBootstrap.program_runs p.val.1 p.val.2
    refine ⟨steps, ?_, hrun⟩
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    exact hsteps.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right p.property 1) 2))

/-- Read a dimension as a unary count and leave all following fields untouched. -/
noncomputable def decodeBoundedNatField :
    Procedure (fun p : BoundedNatField => rawNatField p.val) (prodCode unaryCode id) Subtype.val := by
  let boot : Procedure (fun p : BoundedNatField => rawNatField p.val)
      (prodCode unaryCode rawNatField) (fun p => (p.val.1, p.val)) :=
    boundedNatField.result (by
      intro p
      simp [bootstrappedNatCode, prodCode, pairBits, quoteBits_eq_frame])
  let count := (first unaryCode rawNatField).comp boot
  let refield := (second unaryCode rawNatField).comp boot
  let suffix := (second Nat.bits id).comp (decodeNatField.comp refield)
  exact (count.pair suffix).congrFun (by intro p; rfl)

def rawFields {α : Type} (raw : α → Word) (fields : List α × Word) : Word :=
  fields.1.flatMap raw ++ fields.2

def countedFields {α : Type} (raw : α → Word) (fields : List α × Word) : Word :=
  prodCode unaryCode id (fields.1.length, rawFields raw fields)

abbrev Reader (α : Type) := (List α × Word) × List α

def readerCode {α : Type} (raw native : α → Word) : Reader α → Word :=
  prodCode (countedFields raw) (listCode native)

def readField {α : Type} : Reader α → Reader α
  | (([], suffix), seen) => (([], suffix), seen)
  | ((a :: rest, suffix), seen) => ((rest, suffix), seen ++ [a])

theorem readField_width {α : Type} (raw native : α → Word) (C : ℕ)
    (hRaw : ∀ a, 0 < (raw a).length)
    (hNative : ∀ a, (native a).length ≤ C * (raw a).length)
    (hReverse : ∀ a, (raw a).length ≤ C * ((native a).length + 1))
    (s : Reader α) (steps : ℕ) :
    (readerCode raw native ((readField^[steps]) s)).length ≤
      8 * (C + 1)^2 * ((readerCode raw native s).length + 1) := by
  let rawLength (xs : List α) := (xs.flatMap raw).length
  let nativeLength (xs : List α) := (listCode native xs).length
  have raw_complete (xs : List α) : xs.length ≤ rawLength xs := by
    induction xs with
    | nil => simp [rawLength]
    | cons a xs ih =>
      have ha := hRaw a
      simp only [rawLength, List.length_cons, List.flatMap_cons, List.length_append] at ih ⊢
      omega
  have native_upper (xs : List α) : nativeLength xs ≤ (2 * C + 2) * rawLength xs + 1 := by
    induction xs with
    | nil => simp [rawLength, nativeLength, listCode]
    | cons a xs ih =>
      have ha := hNative a
      have hmin := hRaw a
      have h : 2 * (native a).length + 2 ≤ (2 * C + 2) * (raw a).length := by nlinarith
      simp only [nativeLength, rawLength, List.flatMap_cons, List.length_append,
        listCode_length_cons, Nat.mul_add] at ih ⊢
      omega
  have native_lower (xs : List α) : rawLength xs ≤ C * nativeLength xs := by
    induction xs with
    | nil => simp [rawLength]
    | cons a xs ih =>
      have h := (hReverse a).trans (Nat.mul_le_mul_left C
        (show (native a).length + 1 ≤ 2 * (native a).length + 2 by omega))
      simp only [nativeLength, rawLength, List.flatMap_cons, List.length_append,
        listCode_length_cons, Nat.mul_add] at ih ⊢
      exact (Nat.add_le_add h ih).trans_eq (by ring)
  let mass (s : Reader α) := rawLength s.1.1 + s.1.2.length + rawLength s.2
  have mass_step (s : Reader α) : mass (readField s) = mass s := by
    rcases s with ⟨⟨xs, tail⟩, ys⟩
    cases xs <;> simp [mass, rawLength, readField, List.flatMap_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have mass_iterate (steps : ℕ) : mass ((readField^[steps]) s) = mass s := by
    induction steps with
    | zero => rfl
    | succ steps ih => rw [Function.iterate_succ_apply', mass_step, ih]
  have code_length (s : Reader α) : (readerCode raw native s).length =
      4 * s.1.1.length + 2 * rawLength s.1.1 + 2 * s.1.2.length + nativeLength s.2 + 3 := by
    simp only [readerCode, countedFields, rawFields, rawLength, nativeLength, prodCode,
      pairBits_length, unaryCode, List.length_replicate, List.length_append, id_eq]
    omega
  have width_upper (s : Reader α) : (readerCode raw native s).length ≤ 8 * (C + 1) * (mass s + 1) := by
    rw [code_length]
    have hPend := raw_complete s.1.1
    have hSeen := native_upper s.2
    unfold mass
    nlinarith
  have mass_upper : mass s ≤ (C + 1) * (readerCode raw native s).length := by
    have hSeen := native_lower s.2
    have hA : rawLength s.1.1 + s.1.2.length + nativeLength s.2 ≤
        (readerCode raw native s).length := by rw [code_length]; omega
    apply le_trans _ (Nat.mul_le_mul_left _ hA)
    unfold mass
    nlinarith
  have hInit : mass s + 1 ≤ (C + 1) * ((readerCode raw native s).length + 1) := by
    rw [Nat.mul_succ]
    omega
  calc
    _ ≤ 8 * (C + 1) * (mass ((readField^[steps]) s) + 1) := width_upper _
    _ ≤ 8 * (C + 1) * ((C + 1) * ((readerCode raw native s).length + 1)) := by
      rw [mass_iterate]
      exact Nat.mul_le_mul_left _ hInit
    _ = _ := by ring

noncomputable def readFieldProcedure {α : Type} (raw native : α → Word) (fallback : α)
    (token : Procedure (fun p : α × Word => raw p.1 ++ p.2) (prodCode native id) id) :
    Procedure (readerCode raw native) (readerCode raw native) readField := by
  let pendingCode := rawFields raw
  let seenCode := listCode native
  let tokenRaw (s : α × (List α × Word)) : Word := raw s.1 ++ pendingCode s.2
  let payload := prodCode unaryCode tokenRaw
  let moreData (s : (α × (List α × Word)) × List α) :=
    ((s.1.2.1.length + 1, s.1), s.2)
  let moreCode := prodCode payload seenCode ∘ moreData
  let headBits := (first payload seenCode).precompose moreData
  let tokenBits := (second unaryCode tokenRaw).comp headBits
  let count := (first unaryCode tokenRaw).comp headBits
  let uncount : Procedure moreCode unaryCode (fun s => s.1.2.1.length) :=
    (unaryPred.comp count).congrFun (by intro s; simp [moreData])
  let parse : Procedure tokenRaw (prodCode native pendingCode) id :=
    (token.precompose (fun s : α × (List α × Word) => (s.1, pendingCode s.2))).result
      (by intro s; rfl)
  let parsed := parse.comp tokenBits
  let value := (first native pendingCode).comp parsed
  let rest := (second native pendingCode).comp parsed
  let rawRest : Procedure moreCode id (fun s => pendingCode s.1.2) :=
    rest.result (by intro s; rfl)
  let seen := (second payload seenCode).precompose moreData
  let singleton := (listCons native).comp (value.pair (constant moreCode seenCode []))
  let appended := (Procedure.listAppend (ea := native) fallback).comp (seen.pair singleton)
  let more : Procedure moreCode (readerCode raw native) (fun s => (s.1.2, s.2 ++ [s.1.1])) :=
    ((uncount.pair rawRest).pair appended).result (by intro s; rfl)
  let counts : Procedure (readerCode raw native) (prodCode unaryCode id)
      (fun s => (s.1.1.length, pendingCode s.1)) :=
    (first (countedFields raw) seenCode).result (by intro s; rfl)
  let countWord : Procedure (readerCode raw native) id (fun s => unaryCode s.1.1.length) :=
    ((first unaryCode id).comp counts).result (by intro s; rfl)
  let mark : Procedure (readerCode raw native) id (fun s => [!(unaryCode s.1.1.length).isEmpty]) :=
    (boolNot.comp (Procedure.isEmpty.comp countWord)).result (by intro s; rfl)
  let full : Procedure (readerCode raw native) id (readerCode raw native) :=
    (identity (readerCode raw native)).result (by intro s; rfl)
  let marked : Procedure (readerCode raw native) (sumCode (readerCode raw native) moreCode)
      (fun s => match s.1.1 with
        | [] => .inl s
        | a :: rest => .inr ((a, rest, s.1.2), s.2)) :=
    (Procedure.append.comp (mark.pair full)).result (by
      rintro ⟨⟨xs, suffix⟩, ys⟩
      cases xs <;> simp [readerCode, countedFields, rawFields, moreCode, moreData, tokenRaw,
        pendingCode, seenCode, payload, sumCode, prodCode, unaryCode, List.append_assoc])
  exact ((casesSum (identity (readerCode raw native)) more).comp marked).congrFun (by
    rintro ⟨⟨xs, suffix⟩, ys⟩
    cases xs <;> rfl)

noncomputable def decodeCountedFields {α : Type} (raw native : α → Word) (fallback : α)
    (token : Procedure (fun p : α × Word => raw p.1 ++ p.2) (prodCode native id) id)
    (C : ℕ) (hRaw : ∀ a, 0 < (raw a).length)
    (hNative : ∀ a, (native a).length ≤ C * (raw a).length)
    (hReverse : ∀ a, (raw a).length ≤ C * ((native a).length + 1)) :
    Procedure (countedFields raw) (prodCode (listCode native) id) id := by
  let fieldCode := countedFields raw
  let seenCode := listCode native
  let stageCode := readerCode raw native
  let count : Procedure fieldCode unaryCode (fun x => x.1.length) :=
    (first unaryCode (id : Word → Word)).precompose
      (fun fields : List α × Word => (fields.1.length, rawFields raw fields))
  let initial : Procedure fieldCode stageCode (fun fields => (fields, [])) :=
    (identity fieldCode).pair (constant fieldCode seenCode [])
  let width : Polynomial ℕ := Polynomial.C (8 * (C + 1)^2) * (Polynomial.X + 1)
  let loop := (readFieldProcedure raw native fallback token).iterate width (by
    intro n state i _
    have h := readField_width raw native C hRaw hNative hReverse state i
    simp only [width, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
    exact h.trans (Nat.mul_le_mul_left _ (by omega)))
  let done := loop.comp (count.pair initial)
  let fields : Procedure stageCode (prodCode unaryCode id) (fun s => (s.1.1.length, rawFields raw s.1)) :=
    (first fieldCode seenCode).result (by intro s; rfl)
  let tail := (second unaryCode id).comp fields
  let result := ((second fieldCode seenCode).pair tail).comp done
  have finishes (xs : List α) (suffix : Word) (seen : List α) :
      (readField^[xs.length]) ((xs, suffix), seen) = (([], suffix), seen ++ xs) := by
    induction xs generalizing seen with
    | nil => simp
    | cons a xs ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (readField^[xs.length]) ((xs, suffix), seen ++ [a]) = _
      rw [ih, List.append_assoc]
      rfl
  exact result.congrFun (by
    rintro ⟨xs, suffix⟩
    change (((readField^[xs.length]) ((xs, suffix), [])).2,
      rawFields raw ((readField^[xs.length]) ((xs, suffix), [])).1) = _
    rw [finishes]
    simp [rawFields])

theorem natFields_length (xs : List ℕ) : xs.length ≤ (xs.flatMap encodeNat).length := by
  induction xs with
  | nil => simp
  | cons n xs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.length_append, encodeNat_length]
    omega

noncomputable def decodeNatFields :
    Procedure (countedFields encodeNat) (prodCode (listCode Nat.bits) id) id :=
  decodeCountedFields encodeNat Nat.bits 0 decodeNatField 2
    (by intro n; simp [encodeNat_length])
    (by intro n; rw [encodeNat_length, Nat.size_eq_bits_len]; omega)
    (by intro n; rw [encodeNat_length, Nat.size_eq_bits_len]; omega)

abbrev DecodedInstance := ℕ × ℕ × List ℚ × Word

def decodedInstanceCode : DecodedInstance → Word :=
  prodCode unaryCode (prodCode unaryCode (prodCode (listCode ratCode) id))

def decodeInstance (p : Instance × Word) : DecodedInstance :=
  (p.1.n, p.1.m, (List.ofFn (fun i : p.1.Agent => List.ofFn (p.1.v i))).flatten, p.2)

noncomputable def decodeInstancePrefix :
    Procedure (fun p : Instance × Word => encodeInstance p.1 ++ p.2)
      decodedInstanceCode decodeInstance := by
  let Input := Instance × Word
  let packet (p : Input) := encodeInstance p.1 ++ p.2
  let agents (p : Input) : List ℕ := List.ofFn (fun i : p.1.Agent => i.val)
  let goods (p : Input) : List ℕ := List.ofFn (fun g : p.1.Good => g.val)
  let values (p : Input) : List ℚ := (decodeInstance p).2.2.1
  let valsRaw (p : Input) : Word := rawFields encodeRat (values p, p.2)
  let goodsRaw (p : Input) : Word := rawFields encodeNat (goods p, valsRaw p)
  let agentsRaw (p : Input) : Word := rawFields encodeNat (agents p, goodsRaw p)
  let mRaw (p : Input) : Word := rawNatField (p.1.m, agentsRaw p)
  let nField (p : Input) : BoundedNatField :=
    ⟨(p.1.n, mRaw p), by
      have h := natFields_length (agents p)
      rw [show (agents p).length = p.1.n by simp [agents]] at h
      simp only [rawNatField, mRaw, agentsRaw, rawFields, List.length_append]
      omega⟩
  let mField (p : Input) : BoundedNatField :=
    ⟨(p.1.m, agentsRaw p), by
      have h := natFields_length (goods p)
      rw [show (goods p).length = p.1.m by simp [goods]] at h
      simp only [rawNatField, agentsRaw, goodsRaw, rawFields, List.length_append]
      omega⟩
  let readN : Procedure packet (prodCode unaryCode id) (fun p => (p.1.n, mRaw p)) :=
    (decodeBoundedNatField.precompose nField).congrEncoding (by
      intro p
      simp [nField, rawNatField, mRaw, agentsRaw, goodsRaw, valsRaw, rawFields, values,
        goods, agents, packet, encodeInstance, decodeInstance, List.append_assoc])
      (by intro p; rfl)
  let nCount := (first unaryCode id).comp readN
  let mWord := (second unaryCode id).comp readN
  let mInput : Procedure packet (fun p : BoundedNatField => rawNatField p.val) mField :=
    mWord.result (by intro p; rfl)
  let readM := decodeBoundedNatField.comp mInput
  let mCount := (first unaryCode id).comp readM
  let labelsWord := (second unaryCode id).comp readM
  let agentsInput : Procedure packet (countedFields encodeNat) (fun p => (agents p, goodsRaw p)) :=
    (nCount.pair labelsWord).result (by
      intro p
      simp [countedFields, agents, agentsRaw, mField])
  let afterAgents := (second (listCode Nat.bits) id).comp (decodeNatFields.comp agentsInput)
  let goodsInput : Procedure packet (countedFields encodeNat) (fun p => (goods p, valsRaw p)) :=
    (mCount.pair afterAgents).result (by
      intro p
      simp [countedFields, goods, goodsRaw, mField])
  let afterGoods := (second (listCode Nat.bits) id).comp (decodeNatFields.comp goodsInput)
  let count := unaryMul.comp (nCount.pair mCount)
  have vals_length (p : Input) : (values p).length = p.1.n * p.1.m := by
    simp [values, decodeInstance, List.length_flatten, List.map_ofFn, Function.comp_def, List.sum_ofFn]
  let valsInput : Procedure packet (countedFields encodeRat) (fun p => (values p, p.2)) :=
    (count.pair afterGoods).result (by
      intro p
      change prodCode unaryCode id (p.1.n * p.1.m, valsRaw p) = _
      simp [countedFields, valsRaw, vals_length])
  let readRats := decodeCountedFields encodeRat ratCode (0 : ℚ) PricePacketProcedures.decodeRatField 6
    (by intro q; simp [encodeRat])
    (by
      intro q
      simp only [encodeRat, encodeNat, frame_length, List.length_cons, List.length_append,
        ratCode, intCode, intData, prodCode, pairBits_length, boolCode, List.length_nil]
      omega)
    (by
      intro q
      simp only [encodeRat, encodeNat, frame_length, List.length_cons, List.length_append,
        ratCode, intCode, intData, prodCode, pairBits_length, boolCode, List.length_nil]
      omega)
  exact (nCount.pair (mCount.pair (readRats.comp valsInput))).congrFun (by intro p; rfl)

end EF1FPO.InstanceWire
