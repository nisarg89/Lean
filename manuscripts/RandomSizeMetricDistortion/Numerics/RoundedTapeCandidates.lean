import RandomSizeMetricDistortion.Statements
noncomputable section
namespace MetricDistortion.Contracts.Numerics_RoundedTapeCandidates

private theorem rounded_encloses (bits : ℕ) (I : QInterval) :
    intervalEncloses (tapeRoundInterval bits I) I = true := by
  have hD : (0 : ℚ) < tapeDyadicDen bits := by dsimp [tapeDyadicDen]; positivity
  have hlo : ((Rat.floor (I.lo*tapeDyadicDen bits) : ℤ) : ℚ) ≤ I.lo*tapeDyadicDen bits := Int.floor_le _
  have hhi : ((Rat.floor (-I.hi*tapeDyadicDen bits) : ℤ) : ℚ) ≤ -I.hi*tapeDyadicDen bits := Int.floor_le _
  suffices hp : (tapeRoundInterval bits I).lo ≤ I.lo ∧ I.hi ≤ (tapeRoundInterval bits I).hi by
    simpa only [intervalEncloses,decide_eq_true_eq] using hp
  constructor
  · exact (div_le_iff₀ hD).2 hlo
  · apply (le_div_iff₀ hD).2
    push_cast
    linarith

private theorem row_encloses (bits : ℕ) (preserve : Bool) (row : TapeBounds) :
    tapeBoundsEnclose (tapeRoundRow bits preserve row) row = true := by
  have hself : intervalEncloses row.value row.value = true := by simp [intervalEncloses]
  cases preserve <;> simp [tapeRoundRow,tapeBoundsEnclose,hself,rounded_encloses]

private theorem roundedRows_checked (bits : ℕ) (pick : ℕ → TapeBounds → Bool) (B : Box)
    (ops : List TapeOp) (degrees : List ℕ) (done : List TapeBounds)
    (hv : tapeRefsValidAux done.length ops = true) :
    tapeCheckAux B done ops (roundedTapeRowsAux bits pick B degrees done ops) = true := by
  induction ops generalizing degrees done with
  | nil => rfl
  | cons op ops ih =>
    have hb : tapeRefsValid done.length op = true ∧ tapeRefsValidAux (done.length+1) ops = true := by
      simpa only [tapeRefsValidAux,Bool.and_eq_true_iff] using hv
    simp only [roundedTapeRowsAux,tapeCheckAux,hb.1,row_encloses,Bool.true_and]
    apply ih
    simpa using hb.2

theorem proved : Statement := by
  intro bits pick B tape hv
  exact roundedRows_checked bits pick B tape [] [] hv

#print axioms proved
end MetricDistortion.Contracts.Numerics_RoundedTapeCandidates
