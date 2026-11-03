import FairDivision.Topology.VariableDummyConnectivityZero
import FairDivision.Topology.VariableDummyUniformSlack
import FairDivision.Topology.VariableUniformBridge
import FairDivision.Topology.UnlabeledLottery

/-!
# Unconditional path connectedness for the uniform BF auxiliary complex

This specializes the zero-dimensional corrected-BF induction to the uniform
parameters used in Section 3. It is independent of positive-dimensional
simplicial gluing.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open NerveConnectivity

/-- The uniform restricted auxiliary complex is path connected whenever
the number of positions is positive. -/
theorem variableUniformStock_nullConnected_zero
    {m : ℕ} (n q a : ℕ)
    (D E : Finset (Fin m))
    (hn : 0 < n) (ha : 0 < a) (hq : 2 ≤ q) (hdiv : a ∣ n)
    (hED : Disjoint E D)
    (hTotal : E.card + D.card = n * q) (hD : D.card ≤ n) :
    NullConnectedSet 0
      (simplicialRealization
        (variableStockComplex D E
          (fun _ : Fin (n / a) => a * q - 1) (fun _ => a))) := by
  have hAd := variableUniform_admissible n q a D E ha hq hdiv hTotal hD
  have hSlack := variableUniform_slack n q a D E ha hq hdiv hTotal hD
  have hPos : 0 < n / a := by
    have hMul := Nat.div_mul_cancel hdiv
    by_contra hNot
    have hz : n / a = 0 := by omega
    rw [hz] at hMul
    simp at hMul
    omega
  exact variableStock_nullConnected_zero_of_positiveSlack D E
    (fun _ : Fin (n / a) => a * q - 1) (fun _ => a)
    hED hAd (by rw [hSlack]; exact hPos)

/-- The full corrected BF auxiliary complex, with all nondummy items
available, is unconditionally path connected. -/
theorem uniformUnlabeledDummy_nullConnected_zero
    (n q a : ℕ)
    (D : Finset (Fin (n * q)))
    (hn : 0 < n) (ha : 0 < a) (hq : 2 ≤ q) (hdiv : a ∣ n)
    (hD : D.card ≤ n) :
    NullConnectedSet 0
      (simplicialRealization
        (unlabeledDummyComplex (n / a) (n * q)
          (a * q - 1) a D).toPreAbstractSimplicialComplex) := by
  let E : Finset (Fin (n * q)) := Finset.univ \ D
  have hED : Disjoint E D := Finset.sdiff_disjoint
  have hDuniv : D ⊆ (Finset.univ : Finset (Fin (n * q))) :=
    Finset.subset_univ _
  have hDcard : D.card ≤ n * q := by
    simpa using Finset.card_le_card hDuniv
  have hTotal : E.card + D.card = n * q := by
    dsimp [E]
    rw [Finset.card_sdiff_of_subset hDuniv]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hConn := variableUniformStock_nullConnected_zero
    n q a D E hn ha hq hdiv hED hTotal hD
  change NullConnectedSet 0
    (simplicialRealization
      (variableStockComplex D (Finset.univ \ D)
        (fun _ : Fin (n / a) => a * q - 1) (fun _ => a))) at hConn
  rw [variableStockComplex_full] at hConn
  change NullConnectedSet 0
    (simplicialRealization
      (unlabeledDummyComplex (n / a) (n * q)
        (a * q - 1) a D).toPreAbstractSimplicialComplex) at hConn
  exact hConn

/-- The concrete lottery space used by the BF score map is precisely the
finite-simplex realization of the corrected auxiliary complex. -/
theorem unlabeledLotterySpace_eq_simplicialRealization
    (k m r c : ℕ) (D : Finset (Fin m)) :
    unlabeledLotterySpace k m r c D =
      simplicialRealization
        (unlabeledDummyComplex k m r c D).toPreAbstractSimplicialComplex := by
  ext lot
  change lot ∈ unlabeledLotterySpace k m r c D ↔
    finiteSimplexSupport lot ∈ unlabeledDummyComplex k m r c D
  exact unlabeledLottery_iff_support_face lot

/-- Unconditional path connectedness in the exact lottery-space type on
which the BF auxiliary score is evaluated. -/
theorem uniformUnlabeledLotterySpace_nullConnected_zero
    (n q a : ℕ) (D : Finset (Fin (n * q)))
    (hn : 0 < n) (ha : 0 < a) (hq : 2 ≤ q) (hdiv : a ∣ n)
    (hD : D.card ≤ n) :
    NullConnectedSet 0
      (unlabeledLotterySpace (n / a) (n * q) (a * q - 1) a D) := by
  rw [unlabeledLotterySpace_eq_simplicialRealization]
  exact uniformUnlabeledDummy_nullConnected_zero n q a D hn ha hq hdiv hD

end FairDivision.Topology
