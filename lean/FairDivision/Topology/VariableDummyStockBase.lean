import FairDivision.Topology.VariableDummyBase
import FairDivision.Topology.VariableDummyStockRealization
import FairDivision.Topology.NerveConnectivity.NullHomotopy

/-!
# Zero-requirement base case for the restricted BF complex

If every required bundle has size zero, every auxiliary profile is the same
empty one. The real-stock restriction contains its unique realization point,
so it is null-connected in every dimension.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open NerveConnectivity

/-- A nonempty subsingleton space is null-connected in every dimension. -/
theorem nullConnectedSpace_of_subsingleton
    {X : Type*} [TopologicalSpace X] [Subsingleton X] [Nonempty X]
    (j : ℕ) : NullConnectedSpace j X := by
  refine ⟨‹Nonempty X›, ?_⟩
  intro d _ f
  let x : X := Classical.choice ‹Nonempty X›
  refine ⟨x, ?_⟩
  have hf : f = ContinuousMap.const _ x := by
    ext y
    exact Subsingleton.elim (f y) x
  simpa only [hf] using
    (ContinuousMap.Homotopic.refl (ContinuousMap.const (CubeSphere d) x))

/-- The zero-requirement stock-restricted auxiliary realization is
null-connected, regardless of the stock and dummy caps. -/
theorem variableStock_nullConnected_zero {k m : ℕ}
    {D E : Finset (Fin m)} {r c : Fin k → ℕ}
    (hr : ∀ i : Fin k, r i = 0) (j : ℕ) :
    NullConnectedSet j (variableStockLotterySpace D E r c) := by
  classical
  letI := variableVertex_subsingleton_zero (D := D) (c := c) hr
  have hSub : Subsingleton (variableStockLotterySpace D E r c) := by
    infer_instance
  have hNonempty : Nonempty (variableStockLotterySpace D E r c) := by
    let p := Classical.choice
      (variableVertex_nonempty_zero (D := D) (c := c) hr)
    let lot : stdSimplex ℝ (VariableUnlabeledVertex k m D r c) :=
      stdSimplex.vertex p
    have hWithin : VariableRealWithin E (variableLotterySupport lot) := by
      intro q _ i
      have hcard := variableProfile_card q i
      rw [hr i] at hcard
      have hEmpty : (q.1 i).1 = ∅ := Finset.card_eq_zero.mp (by omega)
      simp [hEmpty]
    have hmem : lot ∈ variableStockLotterySpace D E r c :=
      (mem_variableStockLotterySpace_iff D E r c lot).2
        ⟨variableLotterySpace_all_zero hr lot, hWithin⟩
    exact ⟨⟨lot, hmem⟩⟩
  letI := hSub
  letI := hNonempty
  exact nullConnectedSpace_of_subsingleton j

end FairDivision.Topology
