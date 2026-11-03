import FairDivision.BF.VirtualPoolTransport
import FairDivision.BF.HeterogeneousPositionDummyEndpoint
import FairDivision.BF.VirtualScoreBridge

/-!
# BF Section 5: from a virtual-envy-free auxiliary point to an allocation

This is the manuscript's finite conversion after the virtual valuations and
the topological equalizing point have been constructed. Labeled compatible
representatives provide disjoint position pools. At each position, the
virtual owner witness is translated from the common placeholder to the
actual dummy in that pool. The existing finite completion then gives the
balanced EF[1,1] allocation.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision.Topology
open FairDivision.Finite

/-- For a nonempty dummy set, an auxiliary point satisfying all virtual
owner comparisons yields the manuscript's balanced EF[1,1] allocation. -/
theorem exists_balanced_ef11_of_virtualEnvyFree_nonemptyDummy
    {n N q : ℕ} (D : Finset (Fin N)) (hD : D.Nonempty)
    (v : Fin n → Finset (Fin (N - D.card)) → ℝ)
    (spec : VirtualValuationSpec (q := q) v)
    (x : unlabeledLotterySpace n N (q - 1) 1 D)
    (hVirtualEF : ∀ i j : Fin n,
      spec.score (unlabeledReducedMarginal j x) i ≤
        spec.score (unlabeledReducedMarginal i x) i)
    (hq : 2 ≤ q) (hN : N = n * q) (hDlt : D.card < n) :
    ∃ A : FairDivision.Allocation n (N - D.card),
      FairDivision.IsBalanced A ∧ FairDivision.IsEF11 v A := by
  classical
  obtain ⟨T, hT, _hImage, dummy, hDummyD, hStock⟩ :=
    exists_compatible_pools_for_reducedMarginals hD x
  let E : Fin n → Finset (Fin N) := fun i => pool T i
  let u : Fin n → Fin n → ℝ :=
    fun s i => spec.score (unlabeledReducedMarginal s x) i
  have hWitness (s : Fin n) :
      Nonempty (OwnerWitness q (dummy s)
        (fun j S => v j (pullbackRealBundle D S))
        (E s) (u s) s) := by
    exact virtualScore_ownerWitness_in_actualPool D v spec
      (unlabeledReducedMarginal s x) (E s)
      (dummy s) (hDummyD s) (hStock s) s
  let w (s : Fin n) : OwnerWitness q (dummy s)
      (fun j S => v j (pullbackRealBundle D S))
      (E s) (u s) s := Classical.choice (hWitness s)
  have hEF : ∀ i j : Fin n, u j i ≤ u i i := by
    intro i j
    exact hVirtualEF i j
  have hPools : ∀ i j : Fin n, i ≠ j → Disjoint (E i) (E j) :=
    hT.1
  have hCap : ∀ i : Fin n, (E i ∩ D).card ≤ 1 := hT.2
  exact hetero_positionDummy_selectedWitness_exists_balanced_ef11
    D dummy hDummyD v E u w hq hN hDlt hEF hPools hCap

/-- Score equalization at every positive tolerance, together with the
manuscript's virtual-valuation guarantees, gives the BF allocation when at
least one dummy item was added. -/
theorem exists_balanced_ef11_of_equalized_virtualScores_nonemptyDummy
    {n N q : ℕ} (hn : 0 < n)
    (D : Finset (Fin N)) (hD : D.Nonempty)
    (v : Fin n → Finset (Fin (N - D.card)) → ℝ)
    (spec : VirtualValuationSpec (q := q) v)
    (hEqual : ∀ ε : ℝ, 0 < ε →
      ∃ x : unlabeledLotterySpace n N (q - 1) 1 D,
        ∀ s t : Fin n,
          positionScore hn (fun i z => spec.score z i) ε
            (fun a => unlabeledReducedMarginal a x) s =
          positionScore hn (fun i z => spec.score z i) ε
            (fun a => unlabeledReducedMarginal a x) t)
    (hq : 2 ≤ q) (hN : N = n * q) (hDlt : D.card < n) :
    ∃ A : FairDivision.Allocation n (N - D.card),
      FairDivision.IsBalanced A ∧ FairDivision.IsEF11 v A := by
  obtain ⟨x, hVirtualEF⟩ :=
    exists_virtualEnvyFree_of_equalized_scores hn D v spec hEqual
  exact exists_balanced_ef11_of_virtualEnvyFree_nonemptyDummy
    D hD v spec x hVirtualEF hq hN hDlt

end FairDivision.BF
