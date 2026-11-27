import OAI.Optimization.LinearProgramming.OracleSpec.DialogueDeployment

/-! Finite stack dialogue with complete word replies and word output.
Adapted from the Apache-2.0 OpenAI Math `OracleSpec` dialogue modules at commit
3344da59991ed94f9ba711217b29c1d760badfa6. This version frames a typed word reply
with the unchanged carry and charges the complete reply and output. The upstream
license is available at [the pinned revision](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/LICENSE). -/

set_option autoImplicit false

namespace EF1FPO.WordDialogue

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.Optimization.LinearProgramming.OracleSpec.BitCode
open OAI.Optimization.LinearProgramming.OracleSpec.Dialogue.Ports

variable {I C : Type} {Reply : C → Type} {k : ℕ}

abbrev Event (I C : Type) (Reply : C → Type) := I ⊕ (Σ carry : C, Reply carry)

def inputCode (ei : I → Word) (ec : C → Word) (er : ∀ carry, Reply carry → Word) :
    Event I C Reply → Word
  | .inl i => false :: ei i
  | .inr ⟨carry, reply⟩ => true :: (frame (er carry reply) ++ ec carry)

def actionCode (ec : C → Word) : Word ⊕ (Word × C) → Word
  | .inl output => false :: output
  | .inr (packet, carry) => true :: (frame packet ++ ec carry)

abbrev Dispatch (I C : Type) (Reply : C → Type) := Event I C Reply → Word ⊕ (Word × C)

inductive Session (ei : I → Word) (ec : C → Word) (er : ∀ carry, Reply carry → Word)
    (dispatch : Dispatch I C Reply) (reply : WordOracle) (L : ℕ) :
    Event I C Reply → Transcript → Word → Transcript → ℕ → Prop where
  | done {state hist output} (hDispatch : dispatch state = .inl output)
      (hInput : (inputCode ei ec er state).length ≤ L) (hOutput : output.length ≤ L) :
      Session ei ec er dispatch reply L state hist output hist 1
  | query {state hist packet carry output final rounds} (hDispatch : dispatch state = .inr (packet, carry))
      (hInput : (inputCode ei ec er state).length ≤ L) (hPacket : packet.length ≤ L)
      (hReply : (reply hist packet).length ≤ L)
      (answer : Reply carry) (hEncode : er carry answer = reply hist packet)
      (rest : Session ei ec er dispatch reply L (.inr ⟨carry, answer⟩)
        ((packet, reply hist packet) :: hist) output final rounds) :
      Session ei ec er dispatch reply L state hist output final (rounds + 1)

def nextStep (d : Dialogue.Ports k) : BitCode k :=
  .seq (ofBitStack (unquoteMove d.wire d.io d.tmp d.ctrl))
    (.seq (queryFromStack d.io)
      (.seq (ofBitStack (quoteMove d.io d.wire d.tmp))
        (.seq (.push d.wire true) (.push d.ctrl true))))

def body (d : Dialogue.Ports k) (pureStep : BitCode k) : BitCode k :=
  .seq pureStep (.cases d.wire .skip (drain d.wire) (nextStep d))

def loop (d : Dialogue.Ports k) (pureStep : BitCode k) : BitCode k :=
  .loop d.ctrl .skip (body d pureStep)

def program (d : Dialogue.Ports k) (pureStep : BitCode k) : BitCode k :=
  .seq (.push d.wire false) (.seq (.push d.ctrl true) (loop d pureStep))

theorem nextStep_exec (d : Dialogue.Ports k) (reply : WordOracle) (packet carry : Word) (hist : Transcript) :
    let answer := reply hist packet
    Executes d.io reply (nextStep d) (d.mem (frame packet ++ carry) [] [] [] hist)
      (d.mem (true :: (frame answer ++ carry)) [] [true] [] ((packet, answer) :: hist))
      (10 * packet.length + 8 * answer.length + 15) := by
  let answer := reply hist packet
  let nextHist := (packet, answer) :: hist
  have split := unquoteMove_runs d.wire d.io d.tmp d.ctrl (by simp [wire, io]) (by simp [wire, tmp])
    (by simp [wire, ctrl]) (by simp [io, tmp]) (by simp [io, ctrl]) (by simp [tmp, ctrl])
    packet carry (d.store (frame packet ++ carry) [] []) (by simp [quoteBits_eq_frame])
    (by simp) (by simp)
  have hUnframe := ofBitStack_exec split d.io reply [] hist
  simp only [read_io, List.append_nil, write_wire, write_io] at hUnframe
  have send := queryFromStack_exec d.io d.io reply (d.mem carry packet [] [] hist) rfl
  have hSend : Executes d.io reply (queryFromStack d.io) (d.mem carry packet [] [] hist)
      (d.mem carry answer [] [] nextHist) (3 * packet.length + 2 + answer.length) := by
    simpa [mem, Memory.drained, Memory.receive, nextHist, answer, Nat.add_assoc] using send
  have hQuote := quoteMove_runs d.io d.wire d.tmp (by simp [io, wire]) (by simp [io, tmp])
    (by simp [wire, tmp]) (d.store carry answer []) (by simp)
  have hFrame := ofBitStack_exec hQuote d.io reply [] nextHist
  simp only [read_io, read_wire, write_io, write_wire, quoteBits_eq_frame] at hFrame
  have hTag := Executes.push (answer := d.io) (o := reply)
    (d.mem (frame answer ++ carry) [] [] [] nextHist) d.wire true
  have hFlag := Executes.push (answer := d.io) (o := reply)
    (d.mem (true :: (frame answer ++ carry)) [] [] [] nextHist) d.ctrl true
  simp only [push_wire] at hTag
  simp only [push_ctrl] at hFlag
  change Executes d.io reply _ _ _ (10 * packet.length + 8 * answer.length + 15)
  rw [show 10 * packet.length + 8 * answer.length + 15 =
    (7 * packet.length + 6) + ((3 * packet.length + 2 + answer.length) +
      ((7 * answer.length + 5) + (1 + 1))) by omega]
  exact Executes.seq hUnframe (Executes.seq hSend (Executes.seq hFrame (Executes.seq hTag hFlag)))

theorem loop_exec (d : Dialogue.Ports k) (pureStep : BitCode k) (ei : I → Word) (ec : C → Word)
    (er : ∀ carry, Reply carry → Word) (dispatch : Dispatch I C Reply) (reply : WordOracle) (L P : ℕ)
    (steps : ∀ state hist, (inputCode ei ec er state).length ≤ L → ∃ n ≤ P,
      Executes d.io reply pureStep (d.mem (inputCode ei ec er state) [] [] [] hist)
        (d.mem (actionCode ec (dispatch state)) [] [] [] hist) n)
    {state hist output final rounds} (session : Session ei ec er dispatch reply L state hist output final rounds) :
    ∃ n ≤ rounds * (P + 18 * L + 17), Executes d.io reply (loop d pureStep)
      (d.mem (inputCode ei ec er state) [] [true] [] hist) (d.mem [] [] [] output.reverse final) n := by
  induction session with
  | @done state hist output hDispatch hInput hOutput =>
    obtain ⟨n, hn, hPure⟩ := steps state hist hInput
    rw [hDispatch] at hPure
    have hDrain : Executes d.io reply (drain d.wire) (d.mem output [] [] [] hist)
        (d.mem [] [] [] output.reverse hist) (2 * output.length + 1) := by
      simpa [Memory.drained, mem] using drain_exec d.wire d.io reply (d.mem output [] [] [] hist)
    have hCase : Executes d.io reply (.cases d.wire .skip (drain d.wire) (nextStep d))
        (d.mem (false :: output) [] [] [] hist) (d.mem [] [] [] output.reverse hist)
        (1 + (2 * output.length + 1)) := by
      apply Executes.casesFalse (xs := output) (by simp [mem])
      simpa using hDrain
    have hBody := Executes.seq hPure hCase
    refine ⟨1 + ((n + (1 + (2 * output.length + 1))) + 1), by simp; omega, ?_⟩
    apply Executes.loopTrue (xs := []) (by simp [mem])
    · simpa only [pop_ctrl, List.tail_cons, body] using hBody
    · exact Executes.loopNil (by simp [mem])
  | @query state hist packet carry output final rounds hDispatch hInput hPacket hReply answer hEncode _ ih =>
    obtain ⟨n, hn, hPure⟩ := steps state hist hInput
    obtain ⟨later, hLater, next⟩ := ih
    rw [hDispatch] at hPure
    have hCase : Executes d.io reply (.cases d.wire .skip (drain d.wire) (nextStep d))
        (d.mem (true :: (frame packet ++ ec carry)) [] [] [] hist)
        (d.mem (inputCode ei ec er (.inr ⟨carry, answer⟩)) [] [true] []
          ((packet, reply hist packet) :: hist))
        (1 + (10 * packet.length + 8 * (reply hist packet).length + 15)) := by
      apply Executes.casesTrue (xs := frame packet ++ ec carry) (by simp [mem])
      simpa only [pop_wire, List.tail_cons, inputCode, hEncode] using
        nextStep_exec d reply packet (ec carry) hist
    have hBody := Executes.seq hPure hCase
    refine ⟨1 + ((n + (1 + (10 * packet.length + 8 * (reply hist packet).length + 15))) + later), ?_, ?_⟩
    · rw [Nat.add_mul rounds 1, Nat.one_mul]
      omega
    · apply Executes.loopTrue (xs := []) (by simp [mem])
      · simpa only [pop_ctrl, List.tail_cons, body] using hBody
      · exact next

variable {ei : I → Word} {ec : C → Word} {er : ∀ carry, Reply carry → Word}
  {dispatch : Dispatch I C Reply}

abbrev ProcedureOf (ei : I → Word) (ec : C → Word) (er : ∀ carry, Reply carry → Word)
    (dispatch : Dispatch I C Reply) :=
  Procedure (inputCode ei ec er) (actionCode ec) dispatch

noncomputable def layout (p : ProcedureOf ei ec er dispatch) :
    Dialogue.Ports (Fintype.card (p.shared.K ⊕ Fin 3)) :=
  ⟨(Dialogue.publicPorts p.shared.input).trans (Fintype.equivFin _).toEmbedding⟩

noncomputable def registers (p : ProcedureOf ei ec er dispatch) :
    p.shared.K ↪ Fin (Fintype.card (p.shared.K ⊕ Fin 3)) :=
  (leftEmbed _ (Fin 3)).trans (Fintype.equivFin _).toEmbedding

noncomputable def stepCode (p : ProcedureOf ei ec er dispatch) :
    BitCode (Fintype.card (p.shared.K ⊕ Fin 3)) :=
  ofBitStack (p.shared.program.relabel (registers p))

noncomputable def machine (p : ProcedureOf ei ec er dispatch) : BitProgram :=
  (program (layout p) (stepCode p)).compile (layout p).wire (layout p).io

theorem dispatch_exec (p : ProcedureOf ei ec er dispatch) (reply : WordOracle) (L : ℕ) :
    ∀ state hist, (inputCode ei ec er state).length ≤ L → ∃ n ≤ p.shared.bound.eval L,
      Executes (layout p).io reply (stepCode p) ((layout p).mem (inputCode ei ec er state) [] [] [] hist)
        ((layout p).mem (actionCode ec (dispatch state)) [] [] [] hist) n := by
  classical
  intro state hist hInput
  obtain ⟨n, hn, run⟩ := procedure_exec p.shared (registers p) (fun _ => []) (layout p).io
    reply [] hist state
  refine ⟨n, hn.trans (Procedure.eval_nat_mono _ hInput), ?_⟩
  rw [overlay_singleton, overlay_singleton] at run
  have sameWire : (layout p).wire = (registers p) p.shared.input := rfl
  simpa only [stepCode, mem, store_singleton, sameWire] using run

theorem machine_computes (p : ProcedureOf ei ec er dispatch) (reply : WordOracle)
    {L x output final rounds} (session : Session ei ec er dispatch reply L (.inl x) [] output final rounds) :
    (machine p).ComputesWithin reply (ei x) (rounds * (p.shared.bound.eval L + 18 * L + 17) + 3)
      (fun history bits => history = final ∧ bits = output) := by
  let d := layout p
  obtain ⟨n, hn, run⟩ := loop_exec d (stepCode p) ei ec er dispatch reply L
    (p.shared.bound.eval L) (dispatch_exec p reply L) session
  have tag := Executes.push (answer := d.io) (o := reply)
    (d.mem (ei x) [] [] [] []) d.wire false
  have flag := Executes.push (answer := d.io) (o := reply)
    (d.mem (false :: ei x) [] [] [] []) d.ctrl true
  simp only [push_wire] at tag
  simp only [push_ctrl] at flag
  have complete := Executes.seq tag (Executes.seq flag run)
  rw [← source_start d (ei x)] at complete
  apply compile_computes complete (by omega)
  exact ⟨rfl, List.reverse_reverse output⟩

end EF1FPO.WordDialogue
