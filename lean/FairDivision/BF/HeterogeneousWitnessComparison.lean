import FairDivision.BF.HeterogeneousAdmissibility
import FairDivision.Finite.ShortCount

/-!
# BF Section 5: comparisons for selected virtual-valuation witnesses

For each position choose the bundle certified by the virtual valuation for
that position's owner. If every owner weakly prefers her own virtual score,
the manuscript's pairwise lower/upper bundle comparisons follow immediately.
Compatibility of the position pools keeps all selected bundles disjoint.
-/

set_option autoImplicit false

namespace FairDivision.BF

/-- The manuscript's first conversion inequality, before completing the
partial bundles or removing dummies. The matrix `u s i` is agent `i`'s
virtual value of the marginal lottery at position `s`. -/
theorem selectedWitness_pair_comparison
    {n m q : ℕ} {dummy : Fin m}
    {v : Fin n → Finset (Fin m) → ℝ}
    {E : Fin n → Finset (Fin m)}
    {u : Fin n → Fin n → ℝ}
    (w : ∀ s : Fin n, OwnerWitness q dummy v (E s) (u s) s)
    (hEF : ∀ i j : Fin n, u j i ≤ u i i)
    (i j : Fin n) :
    v i (w j).lowerSet ≤ u j i ∧
    u j i ≤ u i i ∧
    u i i ≤ v i (w i).upperSet := by
  exact ⟨(w j).lower_bound i, hEF i j, (w i).owner_bound⟩

/-- In particular, the lower witness of every position is no better for
agent `i` than the upper witness in her own selected position. -/
theorem selectedWitness_lower_le_ownUpper
    {n m q : ℕ} {dummy : Fin m}
    {v : Fin n → Finset (Fin m) → ℝ}
    {E : Fin n → Finset (Fin m)}
    {u : Fin n → Fin n → ℝ}
    (w : ∀ s : Fin n, OwnerWitness q dummy v (E s) (u s) s)
    (hEF : ∀ i j : Fin n, u j i ≤ u i i)
    (i j : Fin n) :
    v i (w j).lowerSet ≤ v i (w i).upperSet := by
  obtain ⟨hLower, hScore, hUpper⟩ :=
    selectedWitness_pair_comparison w hEF i j
  exact hLower.trans (hScore.trans hUpper)

/-- The selected bundles inherit the disjointness of their position pools. -/
theorem selectedWitness_disjoint
    {n m q : ℕ} {dummy : Fin m}
    {v : Fin n → Finset (Fin m) → ℝ}
    {E : Fin n → Finset (Fin m)}
    {u : Fin n → Fin n → ℝ}
    (w : ∀ s : Fin n, OwnerWitness q dummy v (E s) (u s) s)
    (hPools : ∀ i j : Fin n, i ≠ j → Disjoint (E i) (E j))
    (i j : Fin n) (hij : i ≠ j) :
    Disjoint (w i).B (w j).B :=
  (hPools i j hij).mono (w i).in_stock (w j).in_stock


/-- With `nq` augmented items, precisely one item remains outside the
selected bundles for each selected short bundle. This is the count used in
the first completion phase of the manuscript. -/
theorem selectedWitness_unallocated_count
    {n m q : ℕ} {dummy : Fin m}
    {v : Fin n → Finset (Fin m) → ℝ}
    {E : Fin n → Finset (Fin m)}
    {u : Fin n → Fin n → ℝ}
    (w : ∀ s : Fin n, OwnerWitness q dummy v (E s) (u s) s)
    (hPools : ∀ i j : Fin n, i ≠ j → Disjoint (E i) (E j))
    (U : Finset (Fin m)) (hEU : ∀ i, E i ⊆ U)
    (hq : 1 ≤ q) (hTotal : U.card = n * q) :
    (U \ Finset.univ.biUnion (fun i => (w i).B)).card =
      (Finset.univ.filter (fun i : Fin n => (w i).B.card = q - 1)).card := by
  classical
  have hTotal' : U.card = n * ((q - 1) + 1) := by
    simpa only [Nat.sub_add_cancel hq] using hTotal
  exact FairDivision.Finite.card_unallocated_eq_short_count
    n (q - 1) U (fun i => (w i).B)
    (fun i => (w i).in_stock.trans (hEU i))
    (selectedWitness_disjoint w hPools) hTotal'
    (fun i => (w i).size.elim Or.inl (fun h => Or.inr (by omega)))

end FairDivision.BF
