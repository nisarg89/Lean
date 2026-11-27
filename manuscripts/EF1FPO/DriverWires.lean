import EF1FPO.BisectionDriver
import EF1FPO.ProgressAccess
import EF1FPO.RequestProcedure
import EF1FPO.AnswerProcedure

/-! Pure first-order wire transformations between the certified campaign and word dialogue. -/

set_option autoImplicit false

namespace EF1FPO.BisectionDriver

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.Optimization.LinearProgramming.PriceGame
open PricePacketProcedures

abbrev ReplayJob := Progress × List Bool

def encodeJob : ReplayJob → Word := prodCode encodeProgress id

def replayEvent (job : ReplayJob) : TypedCampaign.Event :=
  match job.2 with
  | [] => .inl job.1.publicInput
  | bit :: prior => .inr (bit, ⟨job.1.publicInput, prior⟩)

structure Pending where
  job : ReplayJob
  query : Query job.1.input.n

abbrev ReplayResult := (Progress × Bool) ⊕ Pending

def encodePending (pending : Pending) : Word :=
  prodCode encodeProgress (prodCode id Control.ecPad)
    (pending.job.1, priceQuery pending.query.index pending.query.prices,
      ⟨pending.job.1.publicInput, pending.job.2⟩)

def encodeReplayResult : ReplayResult → Word :=
  sumCode (prodCode encodeProgress Procedure.boolCode) encodePending

def replayResultAt (job : ReplayJob) : (Bool × List Bool) ⊕ Query job.1.input.n → ReplayResult
  | .inl (bit, _) => .inl (job.1, bit)
  | .inr query => .inr ⟨job, query⟩

def replay (job : ReplayJob) : ReplayResult :=
  replayResultAt job (job.1.observe job.2)

abbrev Resumption := (c : Carry) × Reply c

def encodeResumption (event : Resumption) : Word :=
  prodCode id encodeCarry (encodeReply event.1 event.2, event.1)

def compareAndReplay (event : Resumption) : ReplayJob :=
  (event.1.progress, event.1.compare event.2 :: event.1.replies)

theorem replayEvent_tape (job : ReplayJob) :
    Control.startTape (replayEvent job) = ⟨job.1.publicInput, job.2⟩ := by
  rcases job with ⟨progress, replies⟩
  cases replies <;> rfl

noncomputable def replayInputP :
    Procedure encodeJob (Dialogue.inputCode Control.eiPad Control.ecPad) replayEvent := by
  let progress := first encodeProgress (id : Word → Word)
  let replies := second encodeProgress (id : Word → Word)
  let n := progressAccess.n.comp progress
  let b := progressAccess.b.comp progress
  let k := progressAccess.k.comp progress
  let index := progressAccess.index.comp progress
  let s := unaryAdd.comp ((unaryAdd.comp (b.pair k)).pair (constant encodeJob unaryCode 6))
  let nBinary := Wire.writeNat.comp (unaryToBits.comp n)
  let rangeBinary := Wire.writeNat.comp (double.comp (powTwo.comp s))
  let indexBinary := Wire.writeNat.comp (unaryToBits.comp index)
  let framedN := ((Procedure.quote unaryCode).comp n).result
    (ec := id) (h := fun job => quoteBits (unaryCode job.1.input.n)) (fun _ => rfl)
  let framedReplies := ((Procedure.quote id).comp replies).result
    (ec := id) (h := fun job : ReplayJob => quoteBits job.2) (fun _ => rfl)
  let append {left right : ReplayJob → Word}
      (l : Procedure encodeJob id left) (r : Procedure encodeJob id right) :=
    Procedure.append.comp (l.pair r)
  let tape := append framedReplies (append framedN (append nBinary (append rangeBinary indexBinary)))
  exact tape.result (by
    intro job
    rw [Control.inputCode_pad, replayEvent_tape]
    simp [Function.comp_apply, quoteBits_eq_frame, Control.ecPad, Control.eiPad, Control.encodeInput,
      Control.unaryGoods, priceInput, Progress.publicInput, Progress.s, List.append_assoc])

set_option maxRecDepth 16384 in
noncomputable def replayP : Procedure encodeJob encodeReplayResult replay := by
  have wireAgreement (solver : Control.PublicSolver) (job : ReplayJob) :
      let wire := TypedCampaign.encodeAction (TypedCampaign.dispatch solver (replayEvent job))
      [wire.headD false] ++ (quoteBits (encodeProgress job.1) ++ wire.tail) =
        encodeReplayResult (replayResultAt job (Control.observe (solver job.1.publicInput) job.2.reverse)) := by
    let tape : Control.Tape := ⟨job.1.publicInput, job.2⟩
    let observed : (Bool × List Bool) ⊕ Query tape.input.goods :=
      Control.observe (solver tape.input) tape.reverseReplies.reverse
    have hAction : TypedCampaign.dispatch solver (replayEvent job) =
        TypedCampaign.actionAtTape tape observed :=
      congrArg (TypedCampaign.observeTape solver) (replayEvent_tape job)
    have hCases (value : (Bool × List Bool) ⊕ Query tape.input.goods) :
        let wire := TypedCampaign.encodeAction (TypedCampaign.actionAtTape tape value)
        [wire.headD false] ++ (quoteBits (encodeProgress job.1) ++ wire.tail) =
          encodeReplayResult (replayResultAt job value) := by
      cases value with
      | inl pair => rcases pair with ⟨bit, rest⟩; rfl
      | inr query =>
        simp [TypedCampaign.actionAtTape, tape, TypedCampaign.encodeAction, TypedCampaign.erase,
          Dialogue.actionCode, encodeReplayResult, replayResultAt, encodePending, sumCode,
          prodCode, pairBits, quoteBits_eq_frame] <;> rfl
    dsimp only
    rw [hAction]
    exact hCases observed
  let retain (solver : Control.PublicSolver)
      (typed : Procedure encodeJob TypedCampaign.encodeAction (TypedCampaign.dispatch solver ∘ replayEvent)) :
      Procedure encodeJob encodeReplayResult
        (fun j => replayResultAt j (Control.observe (solver j.1.publicInput) j.2.reverse)) := by
    let flag := (Procedure.head.precompose TypedCampaign.encodeAction).comp typed
    let asWord {f : ReplayJob → Bool} (p : Procedure encodeJob boolCode f) :
        Procedure encodeJob id (fun job => [f job]) :=
      p.result (fun _ => rfl)
    let flagWord := asWord flag
    let tail := (Procedure.tail.precompose TypedCampaign.encodeAction).comp typed
    let progress := first encodeProgress (id : Word → Word)
    let framedProgress : Procedure encodeJob id (fun j => quoteBits (encodeProgress j.1)) :=
      ((Procedure.quote encodeProgress).comp progress).result (fun _ => rfl)
    let attached := Procedure.append.comp (framedProgress.pair tail)
    let packed := Procedure.append.comp (flagWord.pair attached)
    exact packed.result (wireAgreement solver)
  exact retain (Control.campaignSolver Campaign.rounds) (TypedCampaign.procedure.comp replayInputP)

noncomputable def requestActionP :
    Procedure encodePending (WordDialogue.actionCode encodeCarry)
      (fun p => Sum.inr (suspend p.job.1 p.job.2 p.query)) := by
  let tailCode := prodCode (id : Word → Word) Control.ecPad
  let pricesWord (p : Pending) := priceQuery p.query.index p.query.prices
  let fields (p : Pending) :=
    (p.job.1, pricesWord p, (⟨p.job.1.publicInput, p.job.2⟩ : Control.Tape))
  let progress := (first encodeProgress tailCode).precompose fields
  let payload := (second encodeProgress tailCode).precompose fields
  let prices := (first (id : Word → Word) Control.ecPad).comp payload
  let tape := (second (id : Word → Word) Control.ecPad).comp payload
  let n := progressAccess.n.comp progress
  let b := progressAccess.b.comp progress
  let k := progressAccess.k.comp progress
  let index := progressAccess.index.comp progress
  let bounds := progressAccess.bounds.comp progress
  let s := unaryAdd.comp ((unaryAdd.comp (b.pair k)).pair (constant encodePending unaryCode 6))
  let anchor := Wire.writeNat.comp (unaryToBits.comp index)
  let threshold := Wire.writeRat.comp (bisectionThresholdP.comp (k.pair bounds))
  let append {left right : Pending → Word}
      (l : Procedure encodePending id left) (r : Procedure encodePending id right) :=
    Procedure.append.comp (l.pair r)
  let unaryWord {f : Pending → ℕ} (p : Procedure encodePending unaryCode f) :=
    append (p.result (ec := id) (h := fun data => unaryCode (f data)) (fun _ => rfl))
      (constant encodePending id [false])
  let request (p : Pending) := campaignRequest p.job.1.input.b p.job.1.input.k
    p.job.1.index p.job.1.threshold p.query
  let input : Procedure encodePending AnchoredPriceRequest.encode request :=
    (append (unaryWord n) (append (unaryWord s) (append anchor (append threshold prices)))).result
      (by intro p
          simp [fields, pricesWord, Function.comp_apply, request, campaignRequest, encodeUnary,
            AnchoredPriceRequest.encode, Progress.threshold, List.append_assoc])
  let output (p : Pending) :=
    (dyadicQuery p.job.1.s p.job.1.s (request p).grid, encodeRat ((request p).raw p.query.index))
  let result : Procedure encodePending (prodCode (id : Word → Word) id) output :=
    (anchoredRequestProcedure.comp input).result (by
      intro p
      simp [output, prodCode, pairBits, quoteBits_eq_frame, AnchoredPriceRequest.encodeResult,
        request, campaignRequest, Progress.s])
  let grid := (first (id : Word → Word) id).comp result
  let raw := (second (id : Word → Word) id).comp result
  let pricesPayload : Procedure encodePending pricesWord id := prices.result (fun _ => rfl)
  let designatedField : Procedure pricesWord Nat.bits (fun p => p.query.index.val) :=
    ((first Nat.bits (id : Word → Word)).precompose
      (fun p : Pending => (p.query.index.val, (List.ofFn p.query.prices).flatMap encodeRat))).congrEncoding
      (by intro p; simp [prodCode, pairBits, quoteBits_eq_frame, encodeNat, pricesWord, priceQuery])
      (fun _ => rfl)
  let designated := Wire.writeNat.comp (designatedField.comp pricesPayload)
  let replies := Control.priorRepliesP.comp tape
  let framedGrid : Procedure encodePending id (fun p => quoteBits (output p).1) :=
    ((Procedure.quote id).comp grid).result (fun _ => rfl)
  let framedProgress : Procedure encodePending id (fun p => quoteBits (encodeProgress p.job.1)) :=
    ((Procedure.quote encodeProgress).comp progress).result (fun _ => rfl)
  let framedReplies : Procedure encodePending id (fun p => quoteBits p.job.2) :=
    ((Procedure.quote id).comp replies).result (fun _ => rfl)
  let carry := append framedProgress (append framedReplies (append designated raw))
  exact (append (constant encodePending id [true]) (append framedGrid carry)).result (by
    intro p
    simp [Function.comp_apply, output, request, quoteBits_eq_frame, WordDialogue.actionCode, suspend,
      encodeCarry, List.append_assoc])

noncomputable def compareAndReplayP : Procedure encodeResumption encodeJob compareAndReplay := by
  let replyAndCarry (event : Resumption) := (encodeReply event.1 event.2, event.1)
  let answerWord := (first (id : Word → Word) encodeCarry).precompose replyAndCarry
  let carry := (second (id : Word → Word) encodeCarry).precompose replyAndCarry
  let tailCode := prodCode (id : Word → Word) (id : Word → Word)
  let fields (c : Carry) := (c.progress, c.replies, encodeNat c.designated.val ++ encodeRat c.raw)
  let packed : Procedure encodeCarry (prodCode encodeProgress tailCode) fields :=
    ((identity (prodCode encodeProgress tailCode)).precompose fields).congrEncoding
      (by intro c
          simp [encodeCarry, tailCode, fields, prodCode, pairBits, quoteBits_eq_frame, List.append_assoc])
      (fun _ => rfl)
  let unpacked := packed.comp carry
  let progress := (first encodeProgress tailCode).comp unpacked
  let tailFields := (second encodeProgress tailCode).comp unpacked
  let replies := (first (id : Word → Word) id).comp tailFields
  let rawFields := (second (id : Word → Word) id).comp tailFields
  let readN := progressAccess.n.comp progress
  let b := progressAccess.b.comp progress
  let k := progressAccess.k.comp progress
  let readS := unaryAdd.comp ((unaryAdd.comp (b.pair k)).pair (constant encodeResumption unaryCode 6))
  let unaryWord {f : Resumption → ℕ} (p : Procedure encodeResumption unaryCode f) :=
    (Procedure.append.comp ((p.result (ec := id) (h := fun event => unaryCode (f event))
      (fun _ => rfl)).pair (constant encodeResumption id [false])))
  let append {left right : Resumption → Word}
      (l : Procedure encodeResumption id left) (r : Procedure encodeResumption id right) :=
    Procedure.append.comp (l.pair r)
  let wire := append (unaryWord readN) (append (unaryWord readS) (append rawFields answerWord))
  let input : Procedure encodeResumption AnchoredPriceAnswer.encode
      (fun e => ⟨e.1.progress.input.n, e.1.progress.s, e.1.designated, e.1.raw, e.2⟩) :=
    wire.result (by
      intro e
      simp [fields, replyAndCarry, Function.comp_apply, AnchoredPriceAnswer.encode,
        Progress.s, encodeReply, encodeUnary, List.append_assoc])
  let compareBit := anchoredAnswerProcedure.comp input
  let encodedBit : Procedure encodeResumption id (fun event => [event.1.compare event.2]) :=
    compareBit.result (fun _ => rfl)
  exact (progress.pair (append encodedBit replies)).result (fun _ => rfl)

end EF1FPO.BisectionDriver
