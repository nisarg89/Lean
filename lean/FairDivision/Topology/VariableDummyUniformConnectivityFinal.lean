import FairDivision.Topology.VariableDummyUniformConnectivity
import FairDivision.Topology.VariableDummyUniformConnectivityZero
import FairDivision.Topology.NerveConnectivity.OperationalFiniteCover
import FairDivision.Topology.UnlabeledLottery

/-!
# Unconditional uniform connectivity of the corrected BF auxiliary complex

The manuscript's finite-cover induction has already been formalized with a
binary gluing interface. The generic finite-cone/open-cover development now
proves that interface for every finite simplicial complex, so the uniform
full-stock and one-real-item-erased bounds become unconditional.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open NerveConnectivity

/-- The uniform variable-stock complex has its manuscript connectivity
bound, without a binary-gluing premise. -/
theorem variableUniformStock_nullConnected
    {m : ℕ} (n q a : ℕ)
    (D E : Finset (Fin m))
    (hn : 0 < n) (ha : 0 < a) (hq : 2 ≤ q) (hdiv : a ∣ n)
    (hED : Disjoint E D)
    (hTotal : E.card + D.card = n * q) (hD : D.card ≤ n) :
    NullConnectedSet (n / a - 1)
      (simplicialRealization
        (variableStockComplex D E
          (fun _ : Fin (n / a) => a * q - 1) (fun _ => a))) := by
  apply variableUniformStock_nullConnected_of_binaryGluing n q a
    (by intro D' r c; exact operationalBinaryGluing_of_openCover)
    D E hn ha hq hdiv hED hTotal hD

/-- One-real-item-erased uniform stock has the manuscript connectivity
bound whenever at least two positions remain. -/
theorem variableUniformStock_erase_nullConnected
    {m : ℕ} (n q a : ℕ)
    (D E : Finset (Fin m)) (e : Fin m)
    (ha : 0 < a) (hq : 2 ≤ q) (hdiv : a ∣ n)
    (hED : Disjoint E D) (he : e ∈ E)
    (hTotal : E.card + D.card = n * q) (hD : D.card ≤ n)
    (hPositions : 2 ≤ n / a) :
    NullConnectedSet (n / a - 2)
      (simplicialRealization
        (variableStockComplex D (E.erase e)
          (fun _ : Fin (n / a) => a * q - 1) (fun _ => a))) := by
  apply variableUniformStock_erase_nullConnected_of_binaryGluing
    n q a
    (by intro D' r c; exact operationalBinaryGluing_of_openCover)
    D E e ha hq hdiv hED he hTotal hD hPositions

/-- The corrected full auxiliary complex is connected through the degree
asserted in BF Section 3, with no remaining cover-gluing premise. -/
theorem uniformUnlabeledDummy_nullConnected
    (n q a : ℕ)
    (D : Finset (Fin (n * q)))
    (hn : 0 < n) (ha : 0 < a) (hq : 2 ≤ q) (hdiv : a ∣ n)
    (hD : D.card ≤ n) :
    NullConnectedSet (n / a - 1)
      (simplicialRealization
        (unlabeledDummyComplex (n / a) (n * q)
          (a * q - 1) a D).toPreAbstractSimplicialComplex) := by
  apply uniformUnlabeledDummy_nullConnected_of_binaryGluing n q a
    (by intro D' r c; exact operationalBinaryGluing_of_openCover)
    D hn ha hq hdiv hD

/-- The probability-simplex auxiliary space used by BF's score map has
the same uniform connectivity bound. -/
theorem unlabeledLotterySpace_nullConnected
    (n q a : ℕ)
    (D : Finset (Fin (n * q)))
    (hn : 0 < n) (ha : 0 < a) (hq : 2 ≤ q) (hdiv : a ∣ n)
    (hD : D.card ≤ n) :
    NullConnectedSet (n / a - 1)
      (unlabeledLotterySpace (n / a) (n * q)
        (a * q - 1) a D) := by
  rw [unlabeledLotterySpace_eq_simplicialRealization]
  exact uniformUnlabeledDummy_nullConnected n q a D hn ha hq hdiv hD

end FairDivision.Topology
