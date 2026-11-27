import EF1FPO.DriverWires

/-! Separate checked scopes for the controller's actual finite parser and dispatcher. -/

set_option autoImplicit false

namespace EF1FPO.BisectionDriver

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.Optimization.LinearProgramming.PriceGame

noncomputable section

opaque launchProcedure :
    Procedure encodeProgress (WordDialogue.actionCode encodeCarry) launch := by
  let actions := WordDialogue.actionCode encodeCarry
  let completedCode := prodCode encodeProgress boolCode
  let initialJob : Procedure encodeProgress encodeJob (fun p => (p, [])) :=
    (identity encodeProgress).pair (constant encodeProgress id [])
  have agrees (p : Progress) (view : (Bool × List Bool) ⊕ Query p.input.n) :
      Sum.elim (fun _ : Progress × Bool => (.inl [] : Action))
        (fun job : Pending => .inr (suspend job.job.1 job.job.2 job.query))
        (replayResultAt (p, []) view) = launchAction p view := by
    cases view with
    | inl pair => rcases pair with ⟨bit, rest⟩; rfl
    | inr query => rfl
  let compile (inspect : (p : Progress) → List Bool → (Bool × List Bool) ⊕ Query p.input.n)
      (poll : Procedure encodeJob encodeReplayResult
        (fun job => replayResultAt job (inspect job.1 job.2))) :
      Procedure encodeProgress actions (fun p => launchAction p (inspect p [])) :=
    ((casesSum (constant completedCode actions (.inl [] : Action)) requestActionP).comp
      (poll.comp initialJob)).congrFun (fun p => agrees p (inspect p []))
  exact compile Progress.observe replayP

opaque signProcedure :
    Procedure (prodCode encodeProgress Procedure.boolCode)
      (WordDialogue.actionCode encodeCarry) (fun z => afterSign z.1 z.2) := by
  let actions := WordDialogue.actionCode encodeCarry
  let signCode := prodCode encodeProgress boolCode
  let completedCode := listCode intCode
  let progress := first encodeProgress boolCode
  let readBit := second encodeProgress boolCode
  let progressWord : Procedure signCode id (fun z => encodeProgress z.1) :=
    progress.result (fun _ => rfl)
  let bitWord : Procedure signCode id (fun z => [z.2]) := readBit.result (fun _ => rfl)
  let updateInput : Procedure signCode (fun z : Bool × Progress => z.1 :: encodeProgress z.2)
      (fun z => (z.2, z.1)) :=
    (Procedure.append.comp (bitWord.pair progressWord)).result (fun _ => rfl)
  let advances := advanceProcedure.comp updateInput
  let accuracy := progressAccess.k.comp progress
  let carryPrecision := accuracy.pair advances
  let reverse := (Procedure.listReverse (ea := intCode) (0 : ℤ)).comp (second unaryCode completedCode)
  let report := bisectionOutputP.comp ((first unaryCode completedCode).pair reverse)
  let completed : Procedure (prodCode unaryCode completedCode) actions
      (fun z => .inl (bisectionOutput z.1 z.2.reverse)) :=
    ((Procedure.prepend id [false]).comp report).result (fun _ => rfl)
  let compile (start : Progress → Action) (startP : Procedure encodeProgress actions start)
      (fallback : Progress) :
      Procedure signCode actions (fun z => renderAdvance start z.1.input.k (z.1.advance z.2)) := by
    let more := startP.comp (second unaryCode encodeProgress)
    let extend := Control.Native.Join.contextCases ([] : List ℤ) fallback completed more
    exact (extend.comp carryPrecision).congrFun (by
      rintro ⟨p, bit⟩
      simp only [Function.comp_apply, id_eq, renderAdvance]
      cases h : p.advance bit <;> simp only [h])
  exact compile launch launchProcedure (initial ⟨1, 0, 0, by decide⟩)

opaque resumeProcedure :
    Procedure encodeResumption (WordDialogue.actionCode encodeCarry) (fun z => resume z.1 z.2) := by
  let actions := WordDialogue.actionCode encodeCarry
  have agrees (job : ReplayJob) (view : (Bool × List Bool) ⊕ Query job.1.input.n) :
      Sum.elim (fun z : Progress × Bool => afterSign z.1 z.2)
        (fun pending : Pending => .inr (suspend pending.job.1 pending.job.2 pending.query))
        (replayResultAt job view) = actionAt job.1 job.2 view := by
    cases view with
    | inl pair => rcases pair with ⟨bit, rest⟩; rfl
    | inr query => rfl
  let compile (inspect : (p : Progress) → List Bool → (Bool × List Bool) ⊕ Query p.input.n)
      (poll : Procedure encodeJob encodeReplayResult
        (fun job => replayResultAt job (inspect job.1 job.2))) :
      Procedure encodeResumption actions (fun event =>
        let job := compareAndReplay event
        actionAt job.1 job.2 (inspect job.1 job.2)) :=
    ((casesSum signProcedure requestActionP).comp
      (poll.comp compareAndReplayP)).congrFun (fun event =>
        agrees (compareAndReplay event) (inspect (compareAndReplay event).1 (compareAndReplay event).2))
  exact compile Progress.observe replayP

noncomputable def procedure :
    WordDialogue.ProcedureOf encodeInput encodeCarry encodeReply dispatch := by
  let assembled := casesSum (launchProcedure.comp initialProcedure) resumeProcedure
  have agrees (event : WordDialogue.Event Input Carry Reply) :
      Sum.elim (launch ∘ initial) (fun z : Resumption => resume z.1 z.2) event =
        dispatch event := by
    rcases event with input | ⟨carry, answer⟩
    · rw [Sum.elim_inl, Function.comp_apply, dispatch.eq_1]
    · rw [Sum.elim_inr, dispatch.eq_2]
  exact (assembled.congrEncoding (by
    intro event
    cases event with
    | inl input => rfl
    | inr carry =>
      simp only [sumCode, encodeResumption, prodCode, pairBits, quoteBits_eq_frame,
        WordDialogue.inputCode, id_eq])
    (fun _ => rfl)).congrFun agrees

end

end EF1FPO.BisectionDriver
