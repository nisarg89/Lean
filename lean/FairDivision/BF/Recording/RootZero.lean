import FairDivision.BF.Recording.PrimeFactorRecording
import Mathlib.Topology.Order.IntermediateValue

/-!
# The root recording zero

Choose one strict value interval for the finite valuation. On every fixed
recording-graph point the constructed recorder has opposite endpoint
signs, so the intermediate value theorem supplies the manuscript's common
threshold and its actual supported compatible lottery.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace FairDivision.BF.Recording

/-- A single interval strictly containing every value of the finite set
valuation. The same interval can be used throughout prime-factor recursion. -/
theorem exists_recording_interval {m : ℕ} (v : Finset (Fin m) → ℝ) :
    ∃ L H : ℝ, ∃ hLH : L ≤ H,
      (∀ A : Finset (Fin m), L < v A) ∧ (∀ A : Finset (Fin m), v A < H) := by
  classical
  let C : ℝ := ∑ A : Finset (Fin m), |v A|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hBound (A : Finset (Fin m)) : |v A| ≤ C := by
    exact Finset.single_le_sum (fun B _ => abs_nonneg (v B)) (Finset.mem_univ A)
  refine ⟨-C - 1, C + 1, by linarith, ?_, ?_⟩
  · intro A
    have hValueLower : -|v A| ≤ v A := neg_abs_le (v A)
    have hAbsoluteBound : |v A| ≤ C := hBound A
    linarith
  · intro A
    have hValueUpper : v A ≤ |v A| := le_abs_self (v A)
    have hAbsoluteBound : |v A| ≤ C := hBound A
    linarith

/-- Fixing a graph point leaves a continuous function of the target value
with strict opposite endpoint signs. Its zero has exactly the recorder's
lottery certificate, with no additional recovery premise. -/
theorem RecordingFunction.exists_zero_at {n q m : ℕ}
    {v : Finset (Fin m) → ℝ} {L H : ℝ} {hLH : L ≤ H}
    (Φ : RecordingFunction n q m v L H hLH) (b : Space n q m) :
    ∃ t : Set.Icc L H, Certifies v b t.val := by
  letI : PreconnectedSpace (Set.Icc L H) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  let f : Set.Icc L H → ℝ := fun t => Φ.phi (b, t)
  have hf : Continuous f :=
    Φ.phi.continuous.comp (continuous_const.prodMk continuous_id)
  have hL : f (lowerTarget hLH) ≤ 0 := (Φ.negative b).le
  have hH : 0 ≤ f (upperTarget hLH) := (Φ.positive b).le
  have hZero : (0 : ℝ) ∈ Set.range f :=
    intermediate_value_univ (lowerTarget hLH) (upperTarget hLH) hf ⟨hL, hH⟩
  obtain ⟨t, ht⟩ := hZero
  exact ⟨t, Φ.realizes b t ht⟩

/-- Unconditional root certificate at any actual recording-graph point,
for every positive number of agents and every bundle parameter at least two. -/
theorem exists_certifies_at (n q m : ℕ) (hn : 0 < n) (hq : 2 ≤ q)
    (v : Finset (Fin m) → ℝ) (b : Space n q m) :
    ∃ t : ℝ, Certifies v b t := by
  obtain ⟨L, H, hLH, hL, hH⟩ := exists_recording_interval v
  obtain ⟨Φ⟩ := exists_recordingFunction n q m hn hq v L H hLH hL hH
  obtain ⟨t, ht⟩ := Φ.exists_zero_at b
  exact ⟨t.val, ht⟩

end FairDivision.BF.Recording
