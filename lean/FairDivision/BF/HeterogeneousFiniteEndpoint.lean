import FairDivision.BF.HeterogeneousFinalBalance

/-!
# BF Section 5: finite heterogeneous conversion endpoint

This is the manuscript's finite conversion lemma after a compatible lottery
has supplied disjoint selected bundles, threshold comparisons, and certified
shortening of dummy-free full bundles. It fills all real items, removes
dummies, rebalances the real bundles, and reindexes the real stock to produce
a balanced EF[1,1] allocation.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision.Finite

/-- The finite BF Section 5 conversion, conditional only on the selected
augmented bundles and their manuscript certificates. -/
theorem hetero_finite_conversion_exists_balanced_ef11
    {n N r : ℕ} (D : Finset (Fin N))
    (v : Fin n → Finset (Fin (N - D.card)) → ℝ)
    (τ : Fin n → ℝ)
    (B : Fin n → Finset (Fin N))
    (hr : 1 ≤ r)
    (hN : N = n * (r + 1))
    (hDlt : D.card < n)
    (hB : HeteroPartialState r
      (Finset.univ : Finset (Fin N)) D
      (fun j S => v j (pullbackRealBundle D S)) τ B)
    (hShorten : HeteroShortenable r D
      (fun j S => v j (pullbackRealBundle D S)) τ B) :
    ∃ A : FairDivision.Allocation n (N - D.card),
      FairDivision.IsBalanced A ∧ FairDivision.IsEF11 v A := by
  classical
  let w : Fin n → Finset (Fin N) → ℝ :=
    fun j S => v j (pullbackRealBundle D S)
  have hTotal : (Finset.univ : Finset (Fin N)).card =
      n * (r + 1) := by
    simpa using hN
  have hIgnore : ∀ j : Fin n, ∀ S : Finset (Fin N),
      w j (S \ D) = w j S := by
    intro j S
    dsimp [w]
    rw [pullbackRealBundle_sdiff_dummy]
  obtain ⟨R, hR, hSizes, hBrackets⟩ :=
    complete_hetero_real_family
      (Finset.univ : Finset (Fin N)) D w τ B hr
      (Finset.subset_univ D) hTotal hDlt hIgnore hB hShorten
  obtain ⟨A, hBundle, hCard, _, hEF⟩ :=
    exists_allocation_of_hetero_real_family D v τ R
      (fun i => (hR.1 i).1) hR.2.1 hR.2.2 hSizes hBrackets
  refine ⟨A, ?_, hEF⟩
  intro i
  have hBalancedSize := hR.final_balanced_size D hr hN hDlt hSizes i
  rw [hCard i]
  exact hBalancedSize


/-- The manuscript's selected virtual-valuation witnesses, together with
disjoint compatible pools, imply the final balanced EF[1,1] allocation.
The remaining Section 5 work is constructing these witnesses from the
continuous score map and the topological equalization theorem. -/
theorem hetero_selectedWitness_exists_balanced_ef11
    {n N q : ℕ} (D : Finset (Fin N))
    (dummy : Fin N) (hDummyD : dummy ∈ D)
    (v : Fin n → Finset (Fin (N - D.card)) → ℝ)
    (E : Fin n → Finset (Fin N))
    (u : Fin n → Fin n → ℝ)
    (w : ∀ s : Fin n,
      OwnerWitness q dummy
        (fun j S => v j (pullbackRealBundle D S))
        (E s) (u s) s)
    (hq : 2 ≤ q)
    (hN : N = n * q)
    (hDlt : D.card < n)
    (hEF : ∀ i j : Fin n, u j i ≤ u i i)
    (hPools : ∀ i j : Fin n, i ≠ j → Disjoint (E i) (E j))
    (hCap : ∀ i : Fin n, (E i ∩ D).card ≤ 1) :
    ∃ A : FairDivision.Allocation n (N - D.card),
      FairDivision.IsBalanced A ∧ FairDivision.IsEF11 v A := by
  have hState : HeteroPartialState (q - 1)
      (Finset.univ : Finset (Fin N)) D
      (fun j S => v j (pullbackRealBundle D S))
      (fun j => u j j) (fun i => (w i).B) :=
    heteroState_of_selectedWitness w hEF hPools
      (Finset.univ : Finset (Fin N)) D
      (fun i => Finset.subset_univ (E i)) hCap (by omega)
  have hShorten : HeteroShortenable (q - 1) D
      (fun j S => v j (pullbackRealBundle D S))
      (fun j => u j j) (fun i => (w i).B) :=
    heteroShortenable_of_selectedWitness w hEF D hDummyD (by omega)
  have hN' : N = n * (q - 1 + 1) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ q)] using hN
  exact hetero_finite_conversion_exists_balanced_ef11 D v
    (fun j => u j j) (fun i => (w i).B)
    (by omega) hN' hDlt hState hShorten

end FairDivision.BF
