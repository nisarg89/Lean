import FairDivision.Topology.CompatibleLottery

/-!
# Reconstructing a partial allocation from disjoint bundles

This is the basic finite glue used when dummy labels are assigned afresh to
vertices of the auxiliary complex.  Each item's owner is the unique position
whose proposed bundle contains it, if such a position exists.
-/

set_option autoImplicit false

namespace FairDivision.Finite

open FairDivision.Topology

/-- Assign each item in a proposed bundle to that bundle's position. -/
noncomputable def partialAllocationFromBundles {k m : ℕ}
    (B : Fin k → Finset (Fin m)) : PartialAllocation k m :=
  fun g => if h : ∃ i : Fin k, g ∈ B i then
    some (Classical.choose h) else none

/-- Pairwise disjoint proposed bundles are exactly the bundles of the
reconstructed partial allocation. -/
theorem partialBundle_fromBundles {k m : ℕ}
    (B : Fin k → Finset (Fin m))
    (hPair : ∀ i j : Fin k, i ≠ j → Disjoint (B i) (B j))
    (i : Fin k) :
    partialBundle (partialAllocationFromBundles B) i = B i := by
  classical
  ext g
  simp only [partialBundle, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hex : ∃ j : Fin k, g ∈ B j
  · have hc : g ∈ B (Classical.choose hex) := Classical.choose_spec hex
    have hEq : ∀ j : Fin k, g ∈ B j → Classical.choose hex = j := by
      intro j hj
      by_contra hne
      exact (Finset.disjoint_left.mp (hPair _ _ hne)) hc hj
    simp only [partialAllocationFromBundles, dif_pos hex, Option.some.injEq]
    exact ⟨fun h => h ▸ hc, hEq i⟩
  · have hni : g ∉ B i := fun hi => hex ⟨i, hi⟩
    simp [partialAllocationFromBundles, hex, hni]

end FairDivision.Finite
