import FairDivision.Finite.DummyRemovalReindex
import FairDivision.Finite.DummyRemovalArithmetic

/-!
# Final balanced fairness transport after deleting dummies

The reindexed real allocation has floor-or-ceiling bundle sizes and retains
all one-deletion common-threshold comparisons. This is the finite projection
used after the BF manuscript's augmented allocation construction.
-/

set_option autoImplicit false

namespace FairDivision.Finite

open FairDivision

/-- One-deletion brackets on augmented bundles remain optional-deletion
common-threshold comparisons after reindexing the nondummy stock. -/
theorem projectedRealAllocation_commonThreshold {n N : ℕ}
    (A : Allocation n N) (D : Finset (Fin N))
    (v : Finset (Fin (N - D.card)) → ℝ) (t : ℝ)
    (h : ∀ i : Fin n,
      BracketsOneDeletion
        (fun F => v (pullbackRealBundle D F)) (bundle A i) t) :
    HasCommonThreshold v (projectedRealAllocation A D) t := by
  intro i
  obtain ⟨⟨x, hx, hlow⟩, ⟨y, hy, hhigh⟩⟩ := h i
  have hWitness (z : Fin N) (hz : z ∈ bundle A i) :
      CanDeleteOne (pullbackRealBundle D {z})
        (bundle (projectedRealAllocation A D) i) := by
    constructor
    · rw [bundle_projectedRealAllocation]
      exact pullbackRealBundle_mono D
        (Finset.singleton_subset_iff.mpr hz)
    · calc
        (pullbackRealBundle D {z}).card =
            (({z} : Finset (Fin N)) \ D).card :=
          card_pullbackRealBundle D {z}
        _ ≤ ({z} : Finset (Fin N)).card :=
          Finset.card_le_card Finset.sdiff_subset
        _ = 1 := by simp
  have hComm (z : Fin N) :
      bundle (projectedRealAllocation A D) i \
          pullbackRealBundle D {z} =
        pullbackRealBundle D ((bundle A i).erase z) := by
    calc
      bundle (projectedRealAllocation A D) i \
          pullbackRealBundle D {z} =
          pullbackRealBundle D (bundle A i) \
            pullbackRealBundle D {z} := by
              rw [bundle_projectedRealAllocation]
      _ = pullbackRealBundle D (bundle A i \ {z}) :=
        (pullbackRealBundle_sdiff D (bundle A i) {z}).symm
      _ = pullbackRealBundle D ((bundle A i).erase z) := by
        rw [Finset.sdiff_singleton_eq_erase]
  constructor
  · refine ⟨pullbackRealBundle D {x}, hWitness x hx, ?_⟩
    rw [hComm]
    exact hlow
  · refine ⟨pullbackRealBundle D {y}, hWitness y hy, ?_⟩
    rw [hComm]
    exact hhigh

/-- If fewer than `n` dummies pad an `nq`-item allocation, the projected
real allocation is balanced. -/
theorem projectedRealAllocation_balanced {n q : ℕ}
    (A : Allocation n (n * q))
    (D : Finset (Fin (n * q)))
    (hn : 0 < n) (hq : 0 < q) (hD : D.card < n)
    (h : ∀ i : Fin n,
      (bundle A i).card = q ∧ (bundle A i ∩ D).card ≤ 1) :
    IsBalanced (projectedRealAllocation A D) := by
  intro i
  rw [bundle_projectedRealAllocation, card_pullbackRealBundle]
  exact card_removeDummies_isBalancedSize n q (bundle A i) D
    hn hq hD (h i).1 (h i).2

/-- The manuscript's augmented size, dummy cap, and exact-deletion bracket
hypotheses imply balancedness and a common threshold on real items. -/
theorem projectedRealAllocation_balanced_commonThreshold {n q : ℕ}
    (A : Allocation n (n * q))
    (D : Finset (Fin (n * q)))
    (v : Finset (Fin (n * q - D.card)) → ℝ) (t : ℝ)
    (hn : 0 < n) (hq : 0 < q) (hD : D.card < n)
    (h : ∀ i : Fin n,
      (bundle A i).card = q ∧
      BracketsOneDeletion
        (fun F => v (pullbackRealBundle D F)) (bundle A i) t ∧
      (bundle A i ∩ D).card ≤ 1) :
    IsBalanced (projectedRealAllocation A D) ∧
      HasCommonThreshold v (projectedRealAllocation A D) t := by
  refine ⟨projectedRealAllocation_balanced A D hn hq hD ?_,
    projectedRealAllocation_commonThreshold A D v t ?_⟩
  · intro i
    exact ⟨(h i).1, (h i).2.2⟩
  · intro i
    exact (h i).2.1

end FairDivision.Finite
