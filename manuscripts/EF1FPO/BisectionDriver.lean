import EF1FPO.AnchoredTrace
import EF1FPO.BisectionProcedures
import EF1FPO.HeaderProcedures
import EF1FPO.TypedCampaign
import EF1FPO.WordDialogue
import OAI.Computability.QuantumFactoring.BitStackUnary

/-! Persist exactly the public bisection data and the current campaign's binary replies. -/

set_option autoImplicit false

namespace EF1FPO.BisectionDriver

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.Optimization.LinearProgramming.PriceGame
open PricePacketProcedures

structure Input where
  n : ℕ
  b : ℕ
  k : ℕ
  nonempty : 0 < n

structure Progress where
  input : Input
  index : Fin input.n
  round : ℕ
  bounds : ℤ × ℤ
  completed : List ℤ

def initial (input : Input) : Progress :=
  ⟨input, ⟨0, input.nonempty⟩, 0, bisectionInitial input.k, []⟩

def Progress.s (p : Progress) : ℕ := p.input.b + p.input.k + 6

def Progress.publicInput (p : Progress) : Control.PublicInput :=
  ⟨p.input.n, 2 * 2 ^ p.s, p.index⟩

def Progress.threshold (p : Progress) : ℚ := bisectionThreshold p.input.k p.bounds

def Progress.advance (p : Progress) (sign : Bool) : List ℤ ⊕ Progress :=
  let bounds := bisectionNext p.input.k p.bounds sign
  if p.round + 1 < p.input.k + 2 then
    .inr { p with round := p.round + 1, bounds := bounds }
  else
    let completed := bounds.1 :: p.completed
    if h : p.index.val + 1 < p.input.n then
      .inr ⟨p.input, ⟨p.index.val + 1, h⟩, 0, bisectionInitial p.input.k, completed⟩
    else
      .inl completed

def Progress.observe (p : Progress) (replies : List Bool) :
    (Bool × List Bool) ⊕ Query p.input.n :=
  Control.observe (Control.campaignSolver Campaign.rounds p.publicInput) replies.reverse

structure Carry where
  progress : Progress
  replies : List Bool
  designated : Fin progress.input.n
  raw : ℚ

abbrev Reply (carry : Carry) := GridNumerator carry.progress.input.n
abbrev Action := Word ⊕ (Word × Carry)

def suspend (p : Progress) (replies : List Bool) (query : Query p.input.n) :
    Word × Carry :=
  let q := campaignRequest p.input.b p.input.k p.index p.threshold query
  (dyadicQuery p.s p.s q.grid, ⟨p, replies, query.index, q.raw query.index⟩)

def launchAction (p : Progress) : (Bool × List Bool) ⊕ Query p.input.n → Action
  | .inr query => .inr (suspend p [] query)
  | .inl _ => .inl []

def launch (p : Progress) : Action := launchAction p (p.observe [])

def Carry.compare (c : Carry) (answer : Reply c) : Bool :=
  (AnchoredPriceAnswer.mk c.progress.input.n c.progress.s c.designated c.raw answer).compare

def renderAdvance (start : Progress → Action) (k : ℕ) : List ℤ ⊕ Progress → Action
  | .inl coordinates => .inl (bisectionOutput k coordinates.reverse)
  | .inr progress => start progress

def afterSign (p : Progress) (bit : Bool) : Action :=
  renderAdvance launch p.input.k (p.advance bit)

def actionAt (p : Progress) (replies : List Bool) :
    (Bool × List Bool) ⊕ Query p.input.n → Action
  | .inl (bit, _) => afterSign p bit
  | .inr query => .inr (suspend p replies query)

def resume (c : Carry) (answer : Reply c) : Action :=
  let replies := c.compare answer :: c.replies
  actionAt c.progress replies (c.progress.observe replies)

def dispatch : WordDialogue.Dispatch Input Carry Reply
  | .inl input => launch (initial input)
  | .inr ⟨carry, answer⟩ => resume carry answer

def encodeInput (input : Input) : Word := contractionInput input.n input.b input.k

def encodeProgress (p : Progress) : Word :=
  prodCode unaryCode (prodCode unaryCode (prodCode unaryCode
    (prodCode unaryCode (prodCode unaryCode (prodCode boundsCode (listCode intCode))))))
    (p.input.n, p.input.b, p.input.k, p.index.val, p.round, p.bounds, p.completed)

def encodeCarry (carry : Carry) : Word :=
  frame (encodeProgress carry.progress) ++ frame carry.replies ++
    encodeNat carry.designated.val ++ encodeRat carry.raw

def encodeReply (carry : Carry) (answer : Reply carry) : Word := encodeGrid answer

theorem launch_pending (p : Progress) :
    ∃ q : Query p.input.n, launch p = .inr (suspend p [] q) := by
  have visible (solver : Control.PublicSolver) (i : Control.PublicInput)
      (pending : ∃ packet carry, Control.dispatch solver (.inl i) = .inr (packet, carry)) :
      ∃ q : Query i.goods, Control.observe (solver i) [] = .inr q := by
    as_aux_lemma =>
      obtain ⟨packet, carry, hPending⟩ := pending
      obtain ⟨rfl, query, hObserve, _⟩ :=
        (Control.dispatch_query_iff solver (.inl i) packet carry).mp hPending
      exact ⟨query, hObserve⟩
  have hRange : 0 < p.publicInput.range := by
    change 0 < 2 * (2 : ℕ) ^ p.s
    positivity
  have hVisible : ∃ q : Query p.input.n, p.observe [] = .inr q := by
    change ∃ q : Query p.input.n,
      Control.observe (Control.campaignSolver Campaign.rounds p.publicInput) [] = .inr q
    exact visible (Control.campaignSolver Campaign.rounds) p.publicInput
      (campaign_initial_queries p.publicInput hRange)
  obtain ⟨q, hObserve⟩ := hVisible
  exact ⟨q, (show launch p = launchAction p (p.observe []) from rfl).trans
    (congrArg (launchAction p) hObserve)⟩

noncomputable def initialProcedure : Procedure encodeInput encodeProgress initial := by
  let afterB (input : Input) := rawUnaryField (input.k, [])
  let afterN (input : Input) := rawUnaryField (input.b, afterB input)
  let readN : Procedure encodeInput (prodCode unaryCode id)
      (fun d => (d.n, afterN d)) :=
    (decodeUnaryField.precompose (fun d : Input => (d.n, afterN d))).congrEncoding
      (by intro d
          simp [encodeInput, contractionInput, rawUnaryField, encodeUnary, afterN, afterB, List.append_assoc])
      (fun _ => rfl)
  let readB := readSuffix ((second unaryCode id).comp readN)
    (decodeUnaryField.precompose (fun d : Input => (d.b, afterB d)))
  let readK := readSuffix ((second unaryCode id).comp readB)
    (decodeUnaryField.precompose (fun d : Input => (d.k, [])))
  let n := (first unaryCode id).comp readN
  let b := (first unaryCode id).comp readB
  let k := (first unaryCode id).comp readK
  let zero := constant encodeInput unaryCode 0
  let interval := bisectionInitialP.comp k
  let completed := constant encodeInput (listCode intCode) ([] : List ℤ)
  let stateTail := zero.pair (zero.pair (interval.pair completed))
  exact (n.pair (b.pair (k.pair stateTail))).result (fun _ => rfl)

noncomputable def advanceProcedure :
    Procedure (fun z : Bool × Progress => z.1 :: encodeProgress z.2)
      (fun out => sumCode (listCode intCode) encodeProgress out)
      (fun z => z.2.advance z.1) := by
  let doneCode := listCode intCode
  let tailBounds := prodCode boundsCode doneCode
  let tailIndex := prodCode unaryCode tailBounds
  let tailK := prodCode unaryCode tailIndex
  let tailB := prodCode unaryCode tailK
  let tailN := prodCode unaryCode tailB
  let stateCode := prodCode unaryCode tailN
  let fields (p : Progress) :=
    (p.input.n, p.input.b, p.input.k, p.index.val, p.round, p.bounds, p.completed)
  let readN := (first unaryCode tailN).precompose fields
  let afterN := (second unaryCode tailN).precompose fields
  let readB := (first unaryCode tailB).comp afterN
  let afterB := (second unaryCode tailB).comp afterN
  let readK := (first unaryCode tailK).comp afterB
  let afterK := (second unaryCode tailK).comp afterB
  let readIndex := (first unaryCode tailIndex).comp afterK
  let afterIndex := (second unaryCode tailIndex).comp afterK
  let readRound := (first unaryCode tailBounds).comp afterIndex
  let afterRound := (second unaryCode tailBounds).comp afterIndex
  let readBounds := (first boundsCode doneCode).comp afterRound
  let readDone := (second boundsCode doneCode).comp afterRound
  let zero := constant encodeProgress unaryCode 0
  let one := constant encodeProgress unaryCode 1
  let nextRound := unaryAdd.comp (readRound.pair one)
  let nextIndex := unaryAdd.comp (readIndex.pair one)
  let nextK := unaryAdd.comp (readK.pair one)
  let afterNextIndex := unaryAdd.comp (nextIndex.pair one)
  let unaryRat := natToRat.comp unaryToBits
  let haveRound := Arithmetic.ratLe.comp ((unaryRat.comp nextRound).pair (unaryRat.comp nextK))
  let haveIndex := Arithmetic.ratLe.comp ((unaryRat.comp afterNextIndex).pair (unaryRat.comp readN))
  let tag {f : Progress → Word} (bit : Bool) (inner : Procedure encodeProgress id f) :=
    Procedure.append.comp ((constant encodeProgress id [bit]).pair inner)
  let stage (bit : Bool) : Procedure encodeProgress id
      (fun p => sumCode doneCode encodeProgress (p.advance bit)) := by
    let interval : Procedure encodeProgress id
        (fun p => prodCode unaryCode boundsCode (p.input.k, p.bounds)) :=
      (readK.pair readBounds).result (fun _ => rfl)
    let intervalInput : Procedure encodeProgress
        (fun z : Bool × (ℕ × (ℤ × ℤ)) => z.1 :: prodCode unaryCode boundsCode z.2)
        (fun p => (bit, p.input.k, p.bounds)) :=
      (tag bit interval).result (fun _ => rfl)
    let updated := bisectionNextP.comp intervalInput
    let recordDone := ((Procedure.listCons (ea := intCode)).comp
      (((first intCode intCode).comp updated).pair readDone))
    let keptIndex := readIndex.pair (nextRound.pair (updated.pair readDone))
    let newIndex := nextIndex.pair (zero.pair ((bisectionInitialP.comp readK).pair recordDone))
    let sameCoordinate := readN.pair (readB.pair (readK.pair keptIndex))
    let next := readN.pair (readB.pair (readK.pair newIndex))
    let roundWord : Procedure encodeProgress id
        (fun p => stateCode (p.input.n, p.input.b, p.input.k, p.index.val, p.round + 1,
          bisectionNext p.input.k p.bounds bit, p.completed)) :=
      sameCoordinate.result (fun _ => rfl)
    let nextWord : Procedure encodeProgress id
        (fun p => stateCode (p.input.n, p.input.b, p.input.k, p.index.val + 1, 0,
          bisectionInitial p.input.k, (bisectionNext p.input.k p.bounds bit).1 :: p.completed)) :=
      next.result (fun _ => rfl)
    let doneWord : Procedure encodeProgress id
        (fun p => doneCode ((bisectionNext p.input.k p.bounds bit).1 :: p.completed)) :=
      recordDone.result (fun _ => rfl)
    apply (conditional haveRound (tag true roundWord)
      (conditional haveIndex (tag true nextWord) (tag false doneWord))).congrFun
    intro p
    have hRound : p.round + 1 ≤ p.input.k + 1 ↔ p.round + 1 < p.input.k + 2 := by omega
    have hIndex : p.index.val + 1 + 1 ≤ p.input.n ↔ p.index.val + 1 < p.input.n := by omega
    simp only [Function.comp_apply, id_eq, fields, Nat.cast_le, decide_eq_true_eq, hRound, hIndex]
    unfold Progress.advance
    split
    · rfl
    · split <;> rfl
  exact (chooseBit (stage false) (stage true)).result (by
    rintro ⟨bit, p⟩
    cases bit <;> rfl)

end EF1FPO.BisectionDriver
