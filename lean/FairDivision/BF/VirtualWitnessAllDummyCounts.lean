import FairDivision.BF.VirtualWitnessConversion
import FairDivision.BF.VirtualNoDummyTransport

/-!
# BF virtual-witness conversion for every augmented dummy count

The manuscript's virtual valuations use the same placeholder in all
marginals. The finite conversion splits according to whether the augmented
instance has an actual dummy item. This wrapper reunites those cases without
introducing any extra assumption on the valuation.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision.Topology

/-- A virtual-envy-free auxiliary point gives a balanced EF[1,1] allocation,
for both exactly divisible and padded item counts. -/
theorem exists_balanced_ef11_of_virtualEnvyFree
    {n N q : ℕ} (hn : 0 < n)
    (D : Finset (Fin N))
    (v : Fin n → Finset (Fin (N - D.card)) → ℝ)
    (spec : VirtualValuationSpec (q := q) v)
    (x : unlabeledLotterySpace n N (q - 1) 1 D)
    (hVirtualEF : ∀ i j : Fin n,
      spec.score (unlabeledReducedMarginal j x) i ≤
        spec.score (unlabeledReducedMarginal i x) i)
    (hq : 2 ≤ q) (hN : N = n * q) (hDlt : D.card < n) :
    ∃ A : FairDivision.Allocation n (N - D.card),
      FairDivision.IsBalanced A ∧ FairDivision.IsEF11 v A := by
  by_cases hD : D.Nonempty
  · exact exists_balanced_ef11_of_virtualEnvyFree_nonemptyDummy
      D hD v spec x hVirtualEF hq hN hDlt
  · have hEmpty : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    subst D
    exact exists_balanced_ef11_of_virtualEnvyFree_emptyDummy
      hn v spec x hVirtualEF hq hN

/-- Equalization at every positive tolerance, plus the virtual-valuation
specification, yields the BF allocation for every dummy count. -/
theorem exists_balanced_ef11_of_equalized_virtualScores
    {n N q : ℕ} (hn : 0 < n)
    (D : Finset (Fin N))
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
  exact exists_balanced_ef11_of_virtualEnvyFree
    hn D v spec x hVirtualEF hq hN hDlt

end FairDivision.BF
