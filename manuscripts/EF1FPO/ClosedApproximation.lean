import EF1FPO.ClosedOracle
import EF1FPO.EvaluatorProgram
import EF1FPO.EvaluationParameters
import EF1FPO.ControllerProcedure
import EF1FPO.StructuredClosure

/-! Close the actual contraction controller with the checked evaluator. -/

set_option autoImplicit false

namespace EF1FPO.ClosedApproximation

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open EF1FPO.BisectionDriver (Carry Reply encodeInput encodeCarry encodeReply)

noncomputable section

def eventCode : Event → Word := WordDialogue.inputCode encodeInput encodeCarry encodeReply

structure Active where
  prepared : PreparedInput
  event : Event
  valid : eventInput event = source prepared

abbrev Terminal := PreparedInput × Word
abbrev State := Active ⊕ Terminal

def activeCode (x : Active) : Word :=
  frame (inputCode x.prepared) ++ eventCode x.event

def terminalCode : Terminal → Word := prodCode inputCode id
def stateCode : State → Word := sumCode activeCode terminalCode
def initState (d : PreparedInput) : State := .inl ⟨d, .inl (source d), rfl⟩

structure Pending where
  prepared : PreparedInput
  packet : Word
  carry : Carry
  valid : carry.progress.input = source prepared
  request : requestInput prepared packet

def pendingCode (p : Pending) : Word :=
  frame (inputCode p.prepared) ++ frame p.packet ++ encodeCarry p.carry

abbrev DispatchResult := Terminal ⊕ Pending

def dispatchCode : DispatchResult → Word := sumCode terminalCode pendingCode

theorem pending_exists (x : Active) (packet : Word) (carry : Carry)
    (h : BisectionDriver.dispatch x.event = .inr (packet, carry)) :
    Nonempty (requestInput x.prepared packet) := by
  obtain ⟨shape, p, s, q, hCube, hPacket⟩ := dispatch_query_shape x.event packet carry h
  have dimension : carry.progress.input.n = x.prepared.inst.n :=
    congrArg BisectionDriver.Input.n (shape.trans x.valid)
  have castQuery {n m : ℕ} (h : n = m) (q : GridNumerator n) (cube : unitCube (dyadicPoint p q)) :
      ∃ r : GridNumerator m, unitCube (dyadicPoint p r) ∧ dyadicQuery p s r = dyadicQuery p s q := by
    subst m
    exact ⟨q, cube, rfl⟩
  obtain ⟨r, hRated, hWire⟩ := castQuery dimension q hCube
  refine ⟨⟨⟨x.prepared, p, s, r, hRated⟩, rfl, ?_⟩⟩
  rw [hPacket, ← hWire]
  rfl

def inspect (x : Active) : DispatchResult :=
  match h : BisectionDriver.dispatch x.event with
  | .inl result => .inl (x.prepared, result)
  | .inr (packet, carry) => .inr
    ⟨x.prepared, packet, carry, (dispatch_query_shape x.event packet carry h).1.trans x.valid,
      Classical.choice (pending_exists x packet carry h)⟩

def Pending.grid (p : Pending) : Reply p.carry :=
  let h : p.request.val.prepared.inst.n = p.carry.progress.input.n :=
    (congrArg (fun d : PreparedInput => d.inst.n) p.request.property.1).trans
      ((congrArg BisectionDriver.Input.n p.valid).symm)
  cast (congrArg GridNumerator h) p.request.val.rounded

theorem Pending.reply_word (p : Pending) : encodeReply p.carry p.grid = encodeGrid p.request.val.rounded := by
  have castGridWord {n m : ℕ} (h : n = m) (a : GridNumerator n) :
      encodeGrid (cast (congrArg GridNumerator h) a) = encodeGrid a := by
    subst m
    rfl
  exact castGridWord ((congrArg (fun d : PreparedInput => d.inst.n) p.request.property.1).trans
    ((congrArg BisectionDriver.Input.n p.valid).symm)) p.request.val.rounded

def Pending.resume (p : Pending) : State := .inl
  ⟨p.prepared, .inr ⟨p.carry, p.grid⟩, p.valid⟩

def applyResult : DispatchResult → State
  | .inl result => .inr result
  | .inr pending => pending.resume

def next : State → State
  | .inl active => applyResult (inspect active)
  | .inr terminal => .inr terminal

def view : State → PreparedInput × (Event ⊕ Word)
  | .inl active => (active.prepared, .inl active.event)
  | .inr terminal => (terminal.1, .inr terminal.2)

def finalWord : State → Word
  | .inl _ => []
  | .inr terminal => terminal.2

noncomputable def initialProcedure : Procedure inputCode stateCode initState := by
  let framed : Procedure inputCode EvaluationWire.framedInstance (fun d => (d.inst, [])) :=
    (Procedure.quote inputCode).result (by
      intro d
      simp [EvaluationWire.framedInstance, inputCode, quoteBits_eq_frame])
  let raw := EvaluationWire.readFrameProcedure.comp framed
  let tableP := (first EvaluationWire.tableCode id).comp raw
  let n := (first unaryCode EvaluationWire.tableTailCode).comp tableP
  let p := EvaluationWire.tableHeightProcedure.comp tableP
  let b := unaryMul.comp ((constant inputCode unaryCode 16).pair p)
  let k := unaryMul.comp ((constant inputCode unaryCode 9).pair p)
  let unaryWord : Procedure unaryCode id encodeUnary :=
    (Procedure.append.comp (((identity unaryCode).result (ec := id)
      (h := unaryCode) (fun _ => rfl)).pair (constant unaryCode id [false]))).congrFun (fun _ => rfl)
  let header := Procedure.append.comp ((unaryWord.comp n).pair
    (Procedure.append.comp ((unaryWord.comp b).pair (unaryWord.comp k))))
  let event := (Procedure.prepend id [false]).comp header
  let retained := (identity inputCode).pair event
  let activeWord := retained.result (ec := id) (h := fun d =>
    prodCode inputCode id (d, false :: contractionInput d.inst.n
      (16 * weightBits d.inst) (9 * weightBits d.inst))) (by
    intro d
    simp only [contractionInput, List.append_assoc, Function.comp_apply,
      EvaluationWire.decodeTable, EvaluationWire.tableHeight, EvaluationWire.table, weightBits] <;> rfl)
  exact ((Procedure.prepend id [false]).comp activeWord).result (by
    intro d
    simp only [Function.comp_apply, initState, stateCode, sumCode, activeCode, eventCode,
      WordDialogue.inputCode, encodeInput, source, prodCode, pairBits, quoteBits_eq_frame,
      id_eq, List.singleton_append])

noncomputable def inspectProcedure : Procedure activeCode dispatchCode inspect := by
  let incoming (x : Active) : PreparedInput × Event := (x.prepared, x.event)
  let given := (first inputCode eventCode).precompose incoming
  let event := (second inputCode eventCode).precompose incoming
  let dispatched := BisectionDriver.procedure.comp event
  let raw : Procedure (prodCode inputCode eventCode ∘ incoming) id
      (fun x => WordDialogue.actionCode encodeCarry (BisectionDriver.dispatch x.event)) :=
    dispatched.result (fun _ => rfl)
  let tag := Procedure.head.comp raw
  let tagWord : Procedure (prodCode inputCode eventCode ∘ incoming) id
      (fun x => [(WordDialogue.actionCode encodeCarry (BisectionDriver.dispatch x.event)).headD false]) :=
    tag.result (fun _ => rfl)
  let data := given.pair (Procedure.tail.comp raw)
  let dataWord := data.result (ec := id) (h := fun x =>
    prodCode inputCode id (x.prepared, (WordDialogue.actionCode encodeCarry
      (BisectionDriver.dispatch x.event)).tail)) (fun _ => rfl)
  let word := Procedure.append.comp (tagWord.pair dataWord)
  let output : Procedure (prodCode inputCode eventCode ∘ incoming) dispatchCode inspect :=
    word.result (by
      intro x
      simp only [Function.comp_apply, id_eq]
      unfold inspect
      split <;> simp_all only [dispatchCode, sumCode, WordDialogue.actionCode, List.headD_cons,
        List.tail_cons, List.singleton_append, terminalCode, pendingCode, prodCode, pairBits,
        quoteBits_eq_frame, id_eq, List.append_assoc])
  exact output.congrEncoding
    (by intro x; simp only [Function.comp_apply, incoming, prodCode, pairBits, quoteBits_eq_frame, activeCode])
    (fun _ => rfl)

noncomputable def resumeProcedure : Procedure pendingCode stateCode Pending.resume := by
  let packetCarryCode := prodCode id encodeCarry
  let fields (p : Pending) : PreparedInput × (Word × Carry) := (p.prepared, p.packet, p.carry)
  let code : Pending → Word := prodCode inputCode packetCarryCode ∘ fields
  let prepared := (first inputCode packetCarryCode).precompose fields
  let rest := (second inputCode packetCarryCode).precompose fields
  let packet := (first id encodeCarry).comp rest
  let carry := (second id encodeCarry).comp rest
  let encodedRequest : Procedure code EvaluationInput.encode (fun p => p.request.val) :=
    (prepared.pair packet).result (by
      intro p
      rw [p.request.property.2]
      simp only [prodCode, pairBits, quoteBits_eq_frame, id_eq, Function.comp_apply, fields])
  let reply := EvaluationWire.evaluationProcedure.comp encodedRequest
  let received := reply.pair carry
  let event : Procedure code id (fun p => eventCode (.inr ⟨p.carry, p.grid⟩)) :=
    ((Procedure.prepend packetCarryCode [true]).comp received).result (by
      intro p
      simp only [Function.comp_apply, List.singleton_append, eventCode, WordDialogue.inputCode,
        packetCarryCode, prodCode, pairBits, quoteBits_eq_frame, id_eq, Pending.reply_word, fields])
  let bytes := (prepared.pair event).result (ec := id) (h := fun p =>
    activeCode ⟨p.prepared, .inr ⟨p.carry, p.grid⟩, p.valid⟩) (by
      intro p
      simp only [activeCode, prodCode, pairBits, quoteBits_eq_frame, id_eq, fields])
  let done : Procedure code stateCode Pending.resume :=
    ((Procedure.prepend id [false]).comp bytes).result (fun _ => rfl)
  exact done.congrEncoding (by
    intro p
    simp only [code, Function.comp_apply, fields, pendingCode, packetCarryCode, prodCode, pairBits,
      quoteBits_eq_frame, id_eq, List.append_assoc]) (fun _ => rfl)

noncomputable def stepProcedure : Procedure stateCode stateCode next := by
  let terminal : Procedure terminalCode stateCode (fun out => (.inr out : State)) :=
    (Procedure.prepend terminalCode [true]).result (fun _ => rfl)
  let applyP := (casesSum terminal resumeProcedure).comp inspectProcedure
  have branch (value : DispatchResult) :
      Sum.elim (fun out => (.inr out : State)) Pending.resume value = applyResult value := by
    cases value <;> rfl
  exact (casesSum applyP terminal).congrFun (by
    intro s
    cases s with
    | inl a =>
      rw [Sum.elim_inl, Function.comp_apply, next]
      exact branch (inspect a)
    | inr out => rfl)

noncomputable def finalProcedure : Procedure stateCode id finalWord := by
  exact (casesSum (constant activeCode id []) (second inputCode id)).congrFun
    (fun x => by cases x <;> rfl)

structure ClosedRun where
  output : PreparedInput → Word
  procedure : Procedure inputCode id output
  correct : ∀ d, approximateOutput d (output d)

noncomputable def compute : ClosedRun := by
  let ticks := Classical.choose bounded_sessions
  let hTicks := Classical.choose_spec bounded_sessions
  let capacity := Classical.choose hTicks
  have sessions := Classical.choose_spec hTicks
  let width := Polynomial.C 2 * Polynomial.X + Polynomial.C 2 + capacity
  have stopped (d : PreparedInput) (s : State) (e : Event) (word : Word)
      (seen : view s = (d, .inl e)) (done : BisectionDriver.dispatch e = .inl word) :
      view (next s) = (d, .inr word) := by
    rcases s with a | final
    · change (a.prepared, Sum.inl a.event) = (d, .inl e) at seen
      obtain ⟨hPrepared, hEvent⟩ := Prod.mk.inj seen
      have hEq := Sum.inl.inj hEvent
      subst d
      subst e
      change view (applyResult (inspect a)) = (a.prepared, .inr word)
      unfold inspect
      split
      next result h =>
        have same : result = word := Sum.inl.inj (h.symm.trans done)
        cases same
        rfl
      next packet carry h =>
        rw [done] at h
        cases h
    · change (_, Sum.inr _) = (d, .inl e) at seen
      have bad := congrArg Prod.snd seen
      cases bad
  have replied (d : PreparedInput) (s : State) (e : Event) (history : Transcript)
      (packet : Word) (carry : Carry) (response : Reply carry)
      (seen : view s = (d, .inl e)) (ask : BisectionDriver.dispatch e = .inr (packet, carry))
      (same : encodeReply carry response = answer d history packet) :
      view (next s) = (d, .inl (.inr ⟨carry, response⟩)) := by
    rcases s with a | final
    · change (a.prepared, Sum.inl a.event) = (d, .inl e) at seen
      obtain ⟨hPrepared, hEvent⟩ := Prod.mk.inj seen
      have hEq := Sum.inl.inj hEvent
      subst d
      subst e
      change view (applyResult (inspect a)) = (a.prepared, .inl (.inr ⟨carry, response⟩))
      unfold inspect
      split
      next result h =>
        rw [ask] at h
        cases h
      next pkt c h =>
        obtain ⟨hPacket, hCarry⟩ := Prod.mk.inj (Sum.inr.inj (h.symm.trans ask))
        subst pkt
        subst c
        let saved : Pending := ⟨a.prepared, packet, carry,
          (dispatch_query_shape a.event packet carry ask).1.trans a.valid,
          Classical.choice (pending_exists a packet carry ask)⟩
        have raw : encodeReply carry response = encodeReply carry saved.grid :=
          (same.trans (answer_agrees a.prepared packet saved.request history)).trans saved.reply_word.symm
        have decoded : response = saved.grid := encodeGrid_injective _ raw
        change (a.prepared, (Sum.inl (Sum.inr ⟨carry, saved.grid⟩ : Event) : Event ⊕ Word)) =
          (a.prepared, Sum.inl (Sum.inr ⟨carry, response⟩ : Event))
        rw [decoded]
    · change (_, Sum.inr _) = (d, .inl e) at seen
      have bad := congrArg Prod.snd seen
      cases bad
  have absorbing (d : PreparedInput) (s : State) (word : Word)
      (seen : view s = (d, .inr word)) : next s = s ∧ finalWord s = word := by
    rcases s with a | ⟨prepared, final⟩
    · change (_, Sum.inl _) = (d, .inr word) at seen
      have bad := congrArg Prod.snd seen
      cases bad
    · change (_, Sum.inr final) = (d, .inr word) at seen
      have finalEq := Sum.inr.inj (congrArg Prod.snd seen)
      exact ⟨rfl, finalEq⟩
  let run := WordDialogue.closeWithProcedures source view encodeInput encodeCarry encodeReply
    BisectionDriver.dispatch answer initialProcedure stepProcedure finalProcedure ticks capacity width
    (fun _ => rfl) stopped replied absorbing (by
      intro d s context bound
      rcases s with a | ⟨prepared, final⟩
      · change a.prepared = d at context
        change (eventCode a.event).length ≤ _ at bound
        simp only [stateCode, sumCode, activeCode, List.length_cons, List.length_append, frame_length,
          width, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, context]
        omega
      · change prepared = d at context
        change final.length ≤ _ at bound
        simp only [stateCode, sumCode, terminalCode, prodCode, pairBits_length, id_eq,
          List.length_cons, width, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X, context]
        omega) approximateOutput sessions
  exact ⟨_, run.val, run.property⟩

end

end EF1FPO.ClosedApproximation
