import FairDivision.Topology.CompatibleLottery
import FairDivision.Finite.ExpectedValue
import FairDivision.Finite.ExchangeThreshold

/-!
# Choosing a short or full bundle from one equitable lottery position

A position's expected value equals the common threshold. A supported short
bundle may attain that threshold exactly. Otherwise two supported short
bundles lie on opposite sides; a one-item exchange inside their common pool
gives a full bundle with exact one-deletion values bracketing the threshold.
-/

set_option autoImplicit false

open scoped BigOperators

namespace FairDivision.Finite

open FairDivision.Topology

/-- For one position of a compatible lottery, mean equality produces either a
short exact-value bundle or a full exact-deletion bracket bundle. -/
theorem equitable_position_bundle {k m r c : ℕ}
    {D : Finset (Fin m)}
    (lot : stdSimplex ℝ (PartialVertex k D r c))
    (v : Finset (Fin m) → ℝ) (i : Fin k) (t : ℝ)
    (hMean : (∑ X : PartialVertex k D r c,
      lot.1 X * v (partialBundle X.1 i \ D)) = t) :
    ∃ B : Finset (Fin m),
      B ⊆ pool (lotterySupport lot) i ∧
      ((B.card = r ∧ v (B \ D) = t) ∨
        (B.card = r + 1 ∧
          FairDivision.BracketsOneDeletion
            (fun F => v (F \ D)) B t)) := by
  classical
  -- Follow the manuscript's first case before selecting opposite outcomes:
  -- any supported exact-value bundle is selected as a short bundle.
  by_cases hExact : ∃ X ∈ lotterySupport lot,
      v (partialBundle X.1 i \ D) = t
  · obtain ⟨X,hXS,hXt⟩ := hExact
    exact ⟨partialBundle X.1 i,partialBundle_subset_pool hXS i,
      Or.inl ⟨(X.2 i).1,hXt⟩⟩
  have hWeight : ∀ X ∈ (Finset.univ : Finset (PartialVertex k D r c)),
      0 ≤ lot.1 X := by
    intro X _
    exact lot.2.1 X
  have hMass : (∑ X ∈ (Finset.univ : Finset (PartialVertex k D r c)),
      lot.1 X) = 1 := by
    simpa using lot.2.2
  have hMeanNeg : (∑ X : PartialVertex k D r c,
      lot.1 X * (-v (partialBundle X.1 i \ D))) = -t := by
    calc
      (∑ X : PartialVertex k D r c,
        lot.1 X * (-v (partialBundle X.1 i \ D))) =
        -(∑ X : PartialVertex k D r c,
          lot.1 X * v (partialBundle X.1 i \ D)) := by
        simp only [mul_neg, ← Finset.sum_neg_distrib]
      _ = -t := by rw [hMean]
  obtain ⟨Xlo, _, hposlo, hLowNeg⟩ :=
    FairDivision.weighted_average_exists_ge_pos
      (Finset.univ : Finset (PartialVertex k D r c))
      (fun X => lot.1 X)
      (fun X => -v (partialBundle X.1 i \ D))
      (-t) hWeight hMass (by simpa using hMeanNeg)
  obtain ⟨Xhi, _, hposhi, hHigh⟩ :=
    FairDivision.weighted_average_exists_ge_pos
      (Finset.univ : Finset (PartialVertex k D r c))
      (fun X => lot.1 X)
      (fun X => v (partialBundle X.1 i \ D))
      t hWeight hMass (by simpa using hMean)
  have hLow : v (partialBundle Xlo.1 i \ D) ≤ t := by linarith
  have hXloSupp : Xlo ∈ lotterySupport lot :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hposlo⟩
  have hXhiSupp : Xhi ∈ lotterySupport lot :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hposhi⟩
  have hLowNe : v (partialBundle Xlo.1 i \ D) ≠ t := by
    intro hEq
    exact hExact ⟨Xlo,hXloSupp,hEq⟩
  have hHighNe : t ≠ v (partialBundle Xhi.1 i \ D) := by
    intro hEq
    exact hExact ⟨Xhi,hXhiSupp,hEq.symm⟩
  have hStrict : v (partialBundle Xlo.1 i \ D) < t :=
    lt_of_le_of_ne hLow hLowNe
  have hStrictHigh : t < v (partialBundle Xhi.1 i \ D) :=
    lt_of_le_of_ne hHigh hHighNe
  obtain ⟨B,hBU,hBcard,hBracket⟩ :=
    exists_full_bracket_bundle
      (pool (lotterySupport lot) i)
      (partialBundle Xlo.1 i) (partialBundle Xhi.1 i)
      r (fun F => v (F \ D)) t
      (partialBundle_subset_pool hXloSupp i)
      (partialBundle_subset_pool hXhiSupp i)
      (Xlo.2 i).1 (Xhi.2 i).1 hStrict hStrictHigh.le
  exact ⟨B,hBU,Or.inr ⟨hBcard,hBracket⟩⟩

end FairDivision.Finite
