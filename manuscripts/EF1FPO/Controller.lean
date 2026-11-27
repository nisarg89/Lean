import EF1FPO.DriverBounds
import EF1FPO.DriverTrace

/-! Assemble all bisection decisions into the polynomially bounded actual session. -/

set_option autoImplicit false

namespace EF1FPO.BisectionDriver

open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.Optimization.LinearProgramming.PriceGame

noncomputable section

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 16384 in
theorem bounded_session :
    ∃ width count : Polynomial ℕ, ∀ (input : Input) (f : Vector input.n → Vector input.n)
      (v : Vector input.n) (reply : WordOracle),
      MonotoneContraction f input.b → unitCube v → f v = v → ApproximationOracle f reply →
      ∃ output history rounds, rounds ≤ count.eval (input.n + input.b + input.k + 1) ∧
        WordDialogue.Session encodeInput encodeCarry encodeReply dispatch reply
          (width.eval (input.n + input.b + input.k + 1)) (.inl input) [] output history rounds ∧
        (∀ exchange ∈ history, ∃ (p s : ℕ) (a : GridNumerator input.n),
          unitCube (dyadicPoint p a) ∧ exchange.1 = dyadicQuery p s a) ∧
        ∃ (s : ℕ) (a : GridNumerator input.n), unitCube (dyadicPoint s a) ∧
          dist (dyadicPoint s a) v ≤ precisionError input.k ∧
          output = encodeUnary s ++ encodeGrid a := by
  obtain ⟨width, initialWidth, outputWidth, exchangeWidth⟩ := driver_word_bound
  let count : Polynomial ℕ := Polynomial.X ^ 2 * campaignHeight + 1
  let asFunction (input : Input) (v : Vector input.n) (j : ℕ) : ℝ :=
    if hj : j < input.n then v ⟨j, hj⟩ else 0
  have asFunction_apply (input : Input) (v : Vector input.n) (i : Fin input.n) :
      asFunction input v i.val = v i := by
    simp [asFunction, i.isLt]
  have cubeOnIndices (input : Input) (v : Vector input.n) (hv : unitCube v) :
      ∀ j < input.n, -1 ≤ asFunction input v j ∧ asFunction input v j ≤ 1 :=
    fun j hj => by simpa only [asFunction, dif_pos hj] using hv ⟨j, hj⟩
  let goodHistory (input : Input) (history : Transcript) : Prop :=
    ∀ exchange ∈ history, ∃ (r s : ℕ) (a : GridNumerator input.n),
      unitCube (dyadicPoint r a) ∧ exchange.1 = dyadicQuery r s a
  let goodOutput (input : Input) (v : Vector input.n) (output : Word) : Prop :=
    ∃ (s : ℕ) (a : GridNumerator input.n), unitCube (dyadicPoint s a) ∧
      dist (dyadicPoint s a) v ≤ precisionError input.k ∧ output = encodeUnary s ++ encodeGrid a
  have traceHistory {p : Progress} {f : Vector p.input.n → Vector p.input.n}
      {reply : WordOracle} {strategy : Computation p.input.n Bool}
      {before after : Transcript} {bit : Bool} {rounds : ℕ}
      (run : AnchoredTrace f reply p.input.b p.input.k p.index p.threshold strategy before bit after rounds)
      (valid : goodHistory p.input before) : goodHistory p.input after := by
    induction run with
    | done bit history => exact valid
    | @query query next history final bit steps answer cube accuracy wire rest ih =>
      apply ih
      intro exchange hExchange
      rcases List.mem_cons.mp hExchange with rfl | previously
      · let request := campaignRequest p.input.b p.input.k p.index p.threshold query
        exact ⟨p.s, p.s, request.grid, request.grid_correct.1, rfl⟩
      · exact valid exchange previously
  have eqLaunch (p : Progress) (observed : (Bool × List Bool) ⊕ Query p.input.n)
      (queries : ∃ q : Query p.input.n, launchAction p observed = .inr (suspend p [] q)) :
      launchAction p observed = actionAt p [] observed := by
    obtain ⟨q, hQuery⟩ := queries
    cases observed with
    | inl result => rcases result with ⟨bit, rest⟩; cases hQuery
    | inr query => rfl
  have vectorOutput (p : Progress) (v : Vector p.input.n) (xs : List ℤ)
      (length : xs.length = p.input.n)
      (entries : ∀ j < p.input.n, ∃ z, xs.reverse[j]? = some z ∧
        GoodCoordinate p.input.k z (asFunction p.input v j)) :
      goodOutput p.input v (bisectionOutput p.input.k xs.reverse) ∧
        (bisectionOutput p.input.k xs.reverse).length ≤ width.eval p.input.size := by
    let a (i : Fin p.input.n) : ℤ :=
      xs.reverse[i.val]'(by simpa only [List.length_reverse, length] using i.isLt)
    have entry (i : Fin p.input.n) : GoodCoordinate p.input.k (a i) (v i) := by
      obtain ⟨z, hz, hGood⟩ := entries i.val i.isLt
      have inList : i.val < xs.reverse.length := by simpa only [List.length_reverse, length] using i.isLt
      have hValue : a i = z := Option.some.inj ((List.getElem?_eq_getElem inList).symm.trans hz)
      rw [hValue, ← asFunction_apply p.input v i]
      exact hGood
    let s := bisectionGrid p.input.k
    have hCube : unitCube (dyadicPoint s a) := fun i => ⟨(entry i).1, (entry i).2.1⟩
    have hTolerance : 0 ≤ precisionError p.input.k := by unfold precisionError; positivity
    have hDistance : dist (dyadicPoint s a) v ≤ precisionError p.input.k :=
      (dist_pi_le_iff hTolerance).mpr fun i => by rw [Real.dist_eq]; exact (entry i).2.2
    have hList : List.ofFn a = xs.reverse := by
      apply List.ext_getElem
      · simp only [List.length_ofFn, List.length_reverse, length]
      · intro i hi hi'
        simp only [List.getElem_ofFn]
        rfl
    have hEncoded :
        bisectionOutput p.input.k xs.reverse = encodeUnary s ++ encodeGrid a := by
      have hCast : List.ofFn (fun j => (a j : ℚ)) = List.map (fun z : ℤ => (z : ℚ)) xs.reverse := by
        rw [← hList, List.map_ofFn]
        rfl
      simp only [bisectionOutput, encodeGrid, hCast, List.flatMap_map, Function.comp_apply, s]
    refine ⟨⟨s, a, hCube, hDistance, hEncoded⟩, ?_⟩
    rw [hEncoded]
    exact outputWidth p.input a hCube
  have solve (remaining : ℕ) :
      ∀ (p : Progress), p.remaining = remaining → ∀ input : Input, p.input = input →
      ∀ (f : Vector input.n → Vector input.n) (v : Vector input.n) (reply : WordOracle),
      MonotoneContraction f input.b → unitCube v → f v = v → ApproximationOracle f reply →
      p.Valid (asFunction input v) → ∀ (state : Event) (before : Transcript),
      (WordDialogue.inputCode encodeInput encodeCarry encodeReply state).length ≤ width.eval input.size →
      dispatch state = launch p → goodHistory input before →
      ∃ result history rounds, rounds ≤ remaining * campaignHeight.eval input.size + 1 ∧
        WordDialogue.Session encodeInput encodeCarry encodeReply dispatch reply (width.eval input.size)
          state before result history rounds ∧ goodHistory input history ∧ goodOutput input v result := by
    induction remaining using Nat.strong_induction_on with
    | h remaining ih =>
      intro p hRemaining input hInput f v reply hMonotone hCube hFixed hOracle valid state before
        stateWidth firstDispatch historyValid
      subst input
      let H := campaignHeight.eval p.input.size
      let L := width.eval p.input.size
      let strategy := Control.campaignSolver Campaign.rounds p.publicInput
      have hRound : p.round < p.input.k + 2 := valid.1
      have hAgent := p.index.isLt
      have hPositive : 0 < remaining := by
        have hFactor : 1 ≤ p.input.n - p.index.val := by omega
        have hProduct : p.input.k + 2 ≤ (p.input.n - p.index.val) * (p.input.k + 2) := by
          simpa only [Nat.one_mul] using Nat.mul_le_mul_right (p.input.k + 2) hFactor
        rw [← hRemaining, Progress.remaining]
        omega
      obtain ⟨bit, after, n, hn, trace⟩ := anchoredTrace_exists hOracle p.index p.threshold strategy before
      have hQueries : n ≤ H := hn.trans (campaign_height_bound p)
      have hAfter := traceHistory trace historyValid
      have hRange : 0 < p.publicInput.range := by
        change 0 < 2 * (2 : ℕ) ^ p.s
        positivity
      have forced (positive : Bool)
          (gap : precisionError (p.input.k + 2) ≤ signFactor positive * (v p.index - (p.threshold : ℝ))) :
          bit = positive :=
        Control.campaignSolver_recover p.publicInput hRange _ _
          (anchoredTrace_reaches hMonotone hCube hFixed gap trace)
      have afterUpdate := advance_valid p (asFunction p.input v)
        (cubeOnIndices p.input v hCube) valid bit
        (by
          intro below
          rw [asFunction_apply] at below
          apply forced false
          simp only [signFactor, Bool.false_eq_true, if_false, neg_one_mul]
          linarith only [below])
        (by
          intro above
          rw [asFunction_apply] at above
          apply forced true
          simp only [signFactor, if_true, one_mul]
          linarith only [above])
      let post (result : Word) (history : Transcript) (later : ℕ) : Prop :=
        later ≤ (remaining - 1) * H + 1 ∧ goodHistory p.input history ∧ goodOutput p.input v result
      have finish (current : Event)
          (fits : (WordDialogue.inputCode encodeInput encodeCarry encodeReply current).length ≤ L)
          (currentAction : dispatch current = afterSign p bit) :
          ∃ result history later, post result history later ∧
            WordDialogue.Session encodeInput encodeCarry encodeReply dispatch reply L
              current after result history later := by
        cases hBranch : p.advance bit with
        | inl written =>
          have finalData : written.length = p.input.n ∧
              ∀ j < p.input.n, ∃ z, written.reverse[j]? = some z ∧
                GoodCoordinate p.input.k z (asFunction p.input v j) := by
            simpa only [hBranch, Progress.AdvancePost] using afterUpdate
          obtain ⟨correct, small⟩ := vectorOutput p v written finalData.1 finalData.2
          have prints : dispatch current = .inl (bisectionOutput p.input.k written.reverse) :=
            currentAction.trans (by simp only [afterSign, renderAdvance, hBranch])
          exact ⟨_, after, 1, ⟨by omega, hAfter, correct⟩,
            WordDialogue.Session.done prints fits small⟩
        | inr upcoming =>
          have nextData : upcoming.input = p.input ∧ upcoming.remaining + 1 = p.remaining ∧
              upcoming.Valid (asFunction p.input v) := by
            simpa only [hBranch, Progress.AdvancePost] using afterUpdate
          have smaller : upcoming.remaining < remaining := by omega
          have launches : dispatch current = launch upcoming :=
            currentAction.trans (by simp only [afterSign, renderAdvance, hBranch])
          obtain ⟨result, history, rounds, hTime, session, hHistory, hCorrect⟩ :=
            ih upcoming.remaining smaller upcoming rfl p.input nextData.1 f v reply
              hMonotone hCube hFixed hOracle nextData.2.2 current after fits launches hAfter
          have eqRounds : upcoming.remaining = remaining - 1 := by omega
          refine ⟨result, history, rounds, ⟨?_, hHistory, hCorrect⟩, session⟩
          simpa only [eqRounds, H] using hTime
      have initializes : dispatch state = actionAt p [] (Control.observe strategy []) :=
        firstDispatch.trans (eqLaunch p (p.observe []) (launch_pending p))
      have same (extra : List Bool) : p.observe (extra.reverse ++ []) = Control.observe strategy extra := by
        exact congrArg (Control.observe strategy) (by simp)
      obtain ⟨result, history, later, hLater, session⟩ :=
        splice_campaign trace (exchangeWidth p (asFunction p.input v) valid) post
          finish state [] same stateWidth initializes
      have hSum : (remaining - 1) * H + H = remaining * H := by
        calc
          (remaining - 1) * H + H = (remaining - 1 + 1) * H := by
            simp only [Nat.add_mul, Nat.one_mul]
          _ = remaining * H := by rw [Nat.sub_add_cancel (by omega : 1 ≤ remaining)]
      have hLaterTime : later ≤ (remaining - 1) * H + 1 := hLater.1
      have hBudget : n + later ≤ remaining * H + 1 := by omega
      exact ⟨result, history, n + later, hBudget, session, hLater.2.1, hLater.2.2⟩
  refine ⟨width, count, ?_⟩
  intro input f v reply hMonotone hCube hFixed hOracle
  let start := initial input
  have hFits := initialWidth input
  have hValid := initial_valid input (asFunction input v) (cubeOnIndices input v hCube)
  obtain ⟨result, history, rounds, hRunning, session, hHistory, hOutput⟩ :=
    solve start.remaining start rfl input rfl f v reply hMonotone hCube hFixed hOracle hValid
      (.inl input) [] hFits rfl (by simp [goodHistory])
  have hAtMost : start.remaining ≤ input.size ^ 2 := by
    simp only [start, Progress.remaining, initial, Nat.sub_zero, pow_two]
    refine Nat.mul_le_mul ?_ ?_
    · unfold Input.size; omega
    · have hN := input.nonempty
      unfold Input.size
      omega
  have hRun : rounds ≤ count.eval input.size := by
    have hBound := Nat.add_le_add_right (Nat.mul_le_mul_right (campaignHeight.eval input.size) hAtMost) 1
    simp only [count, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one]
    exact hRunning.trans hBound
  exact ⟨result, history, rounds, hRun, session, hHistory, hOutput⟩

end

end EF1FPO.BisectionDriver
