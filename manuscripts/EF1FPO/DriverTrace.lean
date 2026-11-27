import EF1FPO.BisectionDriver

/-! Convert one actual anchored campaign to a segment of the machine dialogue. -/

set_option autoImplicit false

namespace EF1FPO.BisectionDriver

open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.Optimization.LinearProgramming.PriceGame

abbrev Event := WordDialogue.Event Input Carry Reply

theorem splice_campaign {p : Progress} {reply : WordOracle} {f : Vector p.input.n → Vector p.input.n}
    {L : ℕ} {residual : Computation p.input.n Bool} {history final : Transcript}
    {bit : Bool} {rounds : ℕ}
    (run : AnchoredTrace f reply p.input.b p.input.k p.index p.threshold residual history bit final rounds)
    (width : ∀ (replies : List Bool) (query : Query p.input.n),
      p.observe replies = .inr query → ∀ answer : GridNumerator p.input.n,
      unitCube (dyadicPoint p.s answer) →
      (suspend p replies query).1.length ≤ L ∧ (encodeGrid answer).length ≤ L ∧
        (WordDialogue.inputCode encodeInput encodeCarry encodeReply
          (.inr ⟨(suspend p replies query).2, answer⟩)).length ≤ L)
    (post : Word → Transcript → ℕ → Prop)
    (finish : ∀ state : Event,
      (WordDialogue.inputCode encodeInput encodeCarry encodeReply state).length ≤ L →
      dispatch state = afterSign p bit →
      ∃ output seen later, post output seen later ∧
        WordDialogue.Session encodeInput encodeCarry encodeReply dispatch reply L state final output seen later)
    (state : Event) (replies : List Bool)
    (same : ∀ extra, p.observe (extra.reverse ++ replies) = Control.observe residual extra)
    (hInput : (WordDialogue.inputCode encodeInput encodeCarry encodeReply state).length ≤ L)
    (hAction : dispatch state = actionAt p replies (Control.observe residual [])) :
    ∃ output seen later, post output seen later ∧
      WordDialogue.Session encodeInput encodeCarry encodeReply dispatch reply L
        state history output seen (rounds + later) := by
  induction run generalizing state replies with
  | done bit history =>
    obtain ⟨output, seen, later, hPost, tail⟩ := finish state hInput hAction
    exact ⟨output, seen, later, hPost, by simpa only [Nat.zero_add] using tail⟩
  | @query query next history final bit rounds answer cube accurate wire rest ih =>
    let current := suspend p replies query
    let resumed : Event := .inr ⟨current.2, answer⟩
    let label := (campaignAnswer
      (campaignRequest p.input.b p.input.k p.index p.threshold query) answer).compare
    let newReplies := label :: replies
    have hObserve : p.observe replies = .inr query := same []
    have hPending : dispatch state = .inr current := hAction
    obtain ⟨hPacket, hReply, hNextInput⟩ := width replies query hObserve answer cube
    have hNew (extra : List Bool) :
        p.observe (extra.reverse ++ newReplies) = Control.observe (next label) extra := by
      have hPrefix := same (label :: extra)
      simpa only [newReplies, List.reverse_cons, List.append_assoc, List.singleton_append,
        Control.observe] using hPrefix
    have hNextObserve : p.observe newReplies = Control.observe (next label) [] := hNew []
    have hNextAction : dispatch resumed = actionAt p newReplies (Control.observe (next label) []) := by
      exact (show dispatch resumed = actionAt p newReplies (p.observe newReplies) from rfl).trans
        (congrArg (actionAt p newReplies) hNextObserve)
    obtain ⟨output, seen, later, hPost, tail⟩ :=
      ih finish resumed newReplies hNew hNextInput hNextAction
    have hWire : reply history current.1 = encodeGrid answer := wire
    have tail' : WordDialogue.Session encodeInput encodeCarry encodeReply dispatch reply L
        resumed ((current.1, reply history current.1) :: history) output seen (rounds + later) := by
      rw [hWire]
      exact tail
    refine ⟨output, seen, later, hPost, ?_⟩
    rw [show rounds + 1 + later = (rounds + later) + 1 by omega]
    exact WordDialogue.Session.query hPending hInput hPacket (hWire.symm ▸ hReply)
      answer hWire.symm tail'

end EF1FPO.BisectionDriver
