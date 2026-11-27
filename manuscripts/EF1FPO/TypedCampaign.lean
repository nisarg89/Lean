import EF1FPO.BisectionState
import OAI.Optimization.LinearProgramming.PriceGame.ControlDispatchMachine

/-! A semantic refinement of the certified replay dispatcher with its wire words unchanged. -/

set_option autoImplicit false

namespace EF1FPO.TypedCampaign

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.Optimization.LinearProgramming.PriceGame

abbrev Event := Control.PublicInput ⊕ (Bool × Control.Tape)
abbrev Action := Bool ⊕ ((t : Control.Tape) × Query t.input.goods)

def actionAtTape (t : Control.Tape) : (Bool × List Bool) ⊕ Query t.input.goods → Action
  | .inl (value, _) => .inl value
  | .inr q => .inr ⟨t, q⟩

def observeTape (solver : Control.PublicSolver) (t : Control.Tape) : Action :=
  actionAtTape t (Control.observe (solver t.input) t.reverseReplies.reverse)

def dispatch (solver : Control.PublicSolver) (e : Event) : Action :=
  observeTape solver (Control.startTape e)

def erase : Action → Bool ⊕ (Word × Control.Tape)
  | .inl value => .inl value
  | .inr ⟨t, q⟩ => .inr (priceQuery q.index q.prices, t)

def encodeAction : Action → Word := Dialogue.actionCode Control.ecPad ∘ erase

theorem erase_dispatch (solver : Control.PublicSolver) (e : Event) :
    erase (dispatch solver e) = Control.dispatch solver e := by
  simp only [dispatch, observeTape, Control.dispatch, Control.observeTape]
  cases Control.observe (solver (Control.startTape e).input)
    (Control.startTape e).reverseReplies.reverse with
  | inl value => rcases value with ⟨bit, rest⟩; rfl
  | inr query => rfl

set_option maxRecDepth 16384 in
noncomputable def procedure :
    Procedure (Dialogue.inputCode Control.eiPad Control.ecPad) encodeAction
      (dispatch (Control.campaignSolver Campaign.rounds)) := by
  have encodeEq (solver : Control.PublicSolver) (event : Event) :
      Dialogue.actionCode Control.ecPad (Control.dispatch solver event) =
        encodeAction (dispatch solver event) :=
    congrArg (Dialogue.actionCode Control.ecPad) (erase_dispatch solver event).symm
  exact Control.Native.dispatchProcedure.result
    (encodeEq (Control.campaignSolver Campaign.rounds))

theorem first_query (i : Control.PublicInput) (hRange : 0 < i.range) :
    ∃ (t : Control.Tape) (q : Query t.input.goods),
      dispatch (Control.campaignSolver Campaign.rounds) (.inl i) = .inr ⟨t, q⟩ := by
  obtain ⟨packet, carry, pending⟩ := campaign_initial_queries i hRange
  have hErase := (erase_dispatch (Control.campaignSolver Campaign.rounds) (.inl i)).trans pending
  have lift (action : Action) (hAction : erase action = .inr (packet, carry)) :
      ∃ (t : Control.Tape) (q : Query t.input.goods), action = .inr ⟨t, q⟩ := by
    cases action with
    | inl value => simp [erase] at hAction
    | inr request => exact ⟨request.1, request.2, rfl⟩
  exact lift _ hErase

end EF1FPO.TypedCampaign
