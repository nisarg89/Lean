import FairDivision.Topology.VariableDummyStock
import FairDivision.Topology.VariableDummyRealization
import FairDivision.Topology.NerveConnectivity.SimplicialCover

/-!
# Realization of a restricted real stock

The BF induction keeps the ambient finite label type fixed when an item is
deleted. This file identifies the probability-simplex realization of the
stock-restricted subcomplex with lotteries supported on vertices using only
that stock.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- The realization of the variable-size auxiliary complex on real stock `E`. -/
abbrev variableStockLotterySpace {k m : ℕ}
    (D E : Finset (Fin m)) (r c : Fin k → ℕ) :
    Set (stdSimplex ℝ (VariableUnlabeledVertex k m D r c)) :=
  NerveConnectivity.simplicialRealization (variableStockComplex D E r c)

/-- A lottery lies in the restricted realization precisely when it is a
compatible lottery and every real bundle in its support uses only `E`. -/
theorem mem_variableStockLotterySpace_iff {k m : ℕ}
    (D E : Finset (Fin m)) (r c : Fin k → ℕ)
    (lot : stdSimplex ℝ (VariableUnlabeledVertex k m D r c)) :
    lot ∈ variableStockLotterySpace D E r c ↔
      lot ∈ variableLotterySpace k m D r c ∧
        VariableRealWithin E (variableLotterySupport lot) := by
  change ((variableLotterySupport lot).Nonempty ∧
      IsVariableUnlabeledFamily (variableLotterySupport lot)) ∧
      VariableRealWithin E (variableLotterySupport lot) ↔
    IsVariableUnlabeledFamily (variableLotterySupport lot) ∧
      VariableRealWithin E (variableLotterySupport lot)
  exact ⟨fun h => ⟨h.1.2, h.2⟩,
    fun h => ⟨⟨variableLotterySupport_nonempty lot, h.1⟩, h.2⟩⟩

/-- Restricting the real stock gives a subspace of the unrestricted BF
realization. -/
theorem variableStockLotterySpace_subset {k m : ℕ}
    (D E : Finset (Fin m)) (r c : Fin k → ℕ) :
    variableStockLotterySpace D E r c ⊆
      variableLotterySpace k m D r c := by
  intro lot hlot
  exact (mem_variableStockLotterySpace_iff D E r c lot).1 hlot |>.1

/-- Stock deletion is the realization-level condition that the removed item
is absent from every supported vertex. -/
theorem mem_variableStockLotterySpace_erase_iff {k m : ℕ}
    (D E : Finset (Fin m)) (r c : Fin k → ℕ)
    (e : Fin m)
    (lot : stdSimplex ℝ (VariableUnlabeledVertex k m D r c)) :
    lot ∈ variableStockLotterySpace D (E.erase e) r c ↔
      lot ∈ variableStockLotterySpace D E r c ∧
        VariableItemAbsent (variableLotterySupport lot) e := by
  exact variableStockComplex_erase_iff_absent D E r c e
    (variableLotterySupport lot)

end FairDivision.Topology
