import FairDivision.Finite.EquitablePartialSelection
import FairDivision.Finite.PartialCompletion
import FairDivision.Finite.BundlePartitionAllocation

/-!
# Converting an equitable compatible lottery to a completed allocation

The manuscript first selects one short exact-value or full bracketed bundle
from each compatible pool, then performs its three-phase completion. The
labeled augmented item stock is a finite universe; dummy values are ignored
by lifting the valuation through set difference with the dummy set.
-/

set_option autoImplicit false

open scoped BigOperators

namespace FairDivision.Finite

open FairDivision.Topology

/-- The manuscript's simultaneous short/full selection is precisely an
initial state for the three-phase completion procedure. -/
theorem completionState_of_equitableLottery {n m r : ℕ}
    {D : Finset (Fin m)}
    (lot : stdSimplex ℝ (PartialVertex n D r 1))
    (hComp : lot ∈ compatibleLotterySpace n m r 1 D)
    (v : Finset (Fin m) → ℝ) (t : ℝ)
    (hMean : ∀ i : Fin n,
      (∑ X : PartialVertex n D r 1,
        lot.1 X * v (partialBundle X.1 i \ D)) = t) :
    ∃ B : Fin n → Finset (Fin m),
      PartialCompletionState n r Finset.univ D
        (fun F => v (F \ D)) t B := by
  obtain ⟨B, hChoice, hPair, hCap⟩ :=
    equitable_partial_selection lot hComp v t hMean
  refine ⟨B, ?_⟩
  refine ⟨?_, hPair, hCap⟩
  intro i
  constructor
  · exact Finset.subset_univ _
  · rcases (hChoice i).2 with hs | hf
    · exact Or.inl hs
    · exact Or.inr hf

/-- An equitable compatible lottery supplies a complete, full-size,
one-dummy-capped partition whose bundles bracket its common value. -/
theorem fullBundles_of_equitableLottery {n m r : ℕ}
    {D : Finset (Fin m)}
    (hm : m = n * (r + 1)) (hD : D.card ≤ n)
    (lot : stdSimplex ℝ (PartialVertex n D r 1))
    (hComp : lot ∈ compatibleLotterySpace n m r 1 D)
    (v : Finset (Fin m) → ℝ) (t : ℝ)
    (hMean : ∀ i : Fin n,
      (∑ X : PartialVertex n D r 1,
        lot.1 X * v (partialBundle X.1 i \ D)) = t) :
    ∃ B : Fin n → Finset (Fin m),
      (∀ i : Fin n,
        (B i).card = r + 1 ∧
        FairDivision.BracketsOneDeletion (fun F => v (F \ D)) (B i) t ∧
        (B i ∩ D).card ≤ 1) ∧
      (∀ i j : Fin n, i ≠ j → Disjoint (B i) (B j)) ∧
      Finset.univ.biUnion B = (Finset.univ : Finset (Fin m)) := by
  obtain ⟨C, hC⟩ := completionState_of_equitableLottery lot hComp v t hMean
  have hTotal : (Finset.univ : Finset (Fin m)).card = n * (r + 1) := by
    simpa using hm
  obtain ⟨B, hB, hFull, hCover⟩ :=
    complete_partial_bundles n r Finset.univ D
      (fun F => v (F \ D)) t hTotal hD C hC
  refine ⟨B, ?_, hB.2.1, hCover⟩
  intro i
  exact ⟨hFull i, hB.full_bracket i (hFull i), hB.2.2 i⟩

/-- The selected and completed bundle partition determines an augmented
allocation with the manuscript's exact threshold and dummy cap. -/
theorem allocation_of_equitableLottery {n m r : ℕ}
    {D : Finset (Fin m)}
    (hm : m = n * (r + 1)) (hD : D.card ≤ n)
    (lot : stdSimplex ℝ (PartialVertex n D r 1))
    (hComp : lot ∈ compatibleLotterySpace n m r 1 D)
    (v : Finset (Fin m) → ℝ) (t : ℝ)
    (hMean : ∀ i : Fin n,
      (∑ X : PartialVertex n D r 1,
        lot.1 X * v (partialBundle X.1 i \ D)) = t) :
    ∃ A : FairDivision.Allocation n m,
      ∀ i : Fin n,
        (FairDivision.bundle A i).card = r + 1 ∧
        FairDivision.BracketsOneDeletion
          (fun F => v (F \ D)) (FairDivision.bundle A i) t ∧
        (FairDivision.bundle A i ∩ D).card ≤ 1 := by
  obtain ⟨B, hB, hPair, hCover⟩ :=
    fullBundles_of_equitableLottery hm hD lot hComp v t hMean
  obtain ⟨A, hAB⟩ := exists_allocation_of_disjoint_cover B hPair hCover
  refine ⟨A, ?_⟩
  intro i
  rw [hAB i]
  exact hB i

end FairDivision.Finite
