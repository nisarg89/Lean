import FairDivision.BF.HeterogeneousFiniteEndpoint

/-!
# BF Section 5: selected witnesses with a dummy label at each position

The virtual valuation uses one placeholder dummy, while a compatible
lottery may use different labeled dummies in different position pools.
After choosing the actual dummy in each pool, shortening certificates are
needed only for full bundles disjoint from the entire dummy set. This is
the selected-witness interface required by the manuscript's conversion.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision.Finite

private theorem localWitness_short_values
    {n m q : ℕ} {dummy : Fin n → Fin m}
    {v : Fin n → Finset (Fin m) → ℝ}
    {E : Fin n → Finset (Fin m)}
    {u : Fin n → Fin n → ℝ}
    (w : ∀ s : Fin n, OwnerWitness q (dummy s) v (E s) (u s) s)
    (hEF : ∀ i j : Fin n, u j i ≤ u i i)
    (i : Fin n) (hi : (w i).B.card = q - 1) :
    (∀ j : Fin n, v j (w i).B ≤ u j j) ∧
      u i i ≤ v i (w i).B := by
  obtain ⟨hLower, hUpper⟩ := (w i).short_sets hi
  constructor
  · intro j
    rw [← hLower]
    exact ((w i).lower_bound j).trans (hEF j i)
  · rw [← hUpper]
    exact (w i).owner_bound

private theorem localWitness_brackets
    {n m q : ℕ} {dummy : Fin n → Fin m}
    {v : Fin n → Finset (Fin m) → ℝ}
    {E : Fin n → Finset (Fin m)}
    {u : Fin n → Fin n → ℝ}
    (w : ∀ s : Fin n, OwnerWitness q (dummy s) v (E s) (u s) s)
    (hEF : ∀ i j : Fin n, u j i ≤ u i i)
    (i : Fin n) :
    HeteroBrackets v (fun j => u j j) i (w i).B := by
  constructor
  · intro j
    let Z := (w i).B \ (w i).lowerSet
    have hDelete := witnessSubset_oneDeletion
      (w i).lower_subset (w i).lower_size (w i).size
    refine ⟨Z, hDelete.1, ?_⟩
    change v j ((w i).B \ Z) ≤ u j j
    rw [hDelete.2]
    exact ((w i).lower_bound j).trans (hEF j i)
  · let Z := (w i).B \ (w i).upperSet
    have hDelete := witnessSubset_oneDeletion
      (w i).upper_subset (w i).upper_size (w i).size
    refine ⟨Z, hDelete.1, ?_⟩
    change u i i ≤ v i ((w i).B \ Z)
    rw [hDelete.2]
    exact (w i).owner_bound

private theorem localWitness_state
    {n m q : ℕ} {dummy : Fin n → Fin m}
    {v : Fin n → Finset (Fin m) → ℝ}
    {E : Fin n → Finset (Fin m)}
    {u : Fin n → Fin n → ℝ}
    (w : ∀ s : Fin n, OwnerWitness q (dummy s) v (E s) (u s) s)
    (hEF : ∀ i j : Fin n, u j i ≤ u i i)
    (hPools : ∀ i j : Fin n, i ≠ j → Disjoint (E i) (E j))
    (U D : Finset (Fin m))
    (hEU : ∀ i, E i ⊆ U)
    (hCap : ∀ i, (E i ∩ D).card ≤ 1)
    (hq : 1 ≤ q) :
    HeteroPartialState (q - 1) U D v (fun j => u j j)
      (fun i => (w i).B) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i
    constructor
    · exact (w i).in_stock.trans (hEU i)
    · rcases (w i).size with hShort | hFull
      · obtain ⟨hLower, hUpper⟩ :=
          localWitness_short_values w hEF i hShort
        exact Or.inl ⟨hShort, hLower, hUpper⟩
      · have hCard : (w i).B.card = q - 1 + 1 := by
          simpa only [Nat.sub_add_cancel hq] using hFull
        exact Or.inr ⟨hCard, localWitness_brackets w hEF i⟩
  · intro i j hij
    exact (hPools i j hij).mono (w i).in_stock (w j).in_stock
  · intro i
    have hSub : (w i).B ∩ D ⊆ E i ∩ D := by
      intro x hx
      exact Finset.mem_inter.mpr
        ⟨(w i).in_stock (Finset.mem_inter.mp hx).1,
          (Finset.mem_inter.mp hx).2⟩
    exact (Finset.card_le_card hSub).trans (hCap i)

private theorem localWitness_shortenable
    {n m q : ℕ} {dummy : Fin n → Fin m}
    {v : Fin n → Finset (Fin m) → ℝ}
    {E : Fin n → Finset (Fin m)}
    {u : Fin n → Fin n → ℝ}
    (w : ∀ s : Fin n, OwnerWitness q (dummy s) v (E s) (u s) s)
    (hEF : ∀ i j : Fin n, u j i ≤ u i i)
    (D : Finset (Fin m)) (hDummyD : ∀ i, dummy i ∈ D)
    (hq : 1 ≤ q) :
    HeteroShortenable (q - 1) D v (fun j => u j j)
      (fun i => (w i).B) := by
  intro i hFull hNoDummySet
  have hFull' : (w i).B.card = q := by
    simpa only [Nat.sub_add_cancel hq] using hFull
  have hNoDummy : dummy i ∉ (w i).B := by
    intro hd
    have hmem : dummy i ∈ (w i).B ∩ D :=
      Finset.mem_inter.mpr ⟨hd, hDummyD i⟩
    simpa [hNoDummySet] using hmem
  obtain ⟨C, hCB, hCard, hLower, hUpper⟩ :=
    (w i).shortening hFull' hNoDummy
  refine ⟨C, hCB, hCard, ?_⟩
  constructor
  · intro j
    obtain ⟨Z, hZ, hVal⟩ := hLower j
    exact ⟨Z, hZ, hVal.trans (hEF j i)⟩
  · exact hUpper

/-- Position-specific dummy labels suffice for the manuscript's finite
conversion from selected support-local witnesses to a balanced EF[1,1]
allocation. -/
theorem hetero_positionDummy_selectedWitness_exists_balanced_ef11
    {n N q : ℕ} (D : Finset (Fin N))
    (dummy : Fin n → Fin N) (hDummyD : ∀ i, dummy i ∈ D)
    (v : Fin n → Finset (Fin (N - D.card)) → ℝ)
    (E : Fin n → Finset (Fin N))
    (u : Fin n → Fin n → ℝ)
    (w : ∀ s : Fin n,
      OwnerWitness q (dummy s)
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
    localWitness_state w hEF hPools
      (Finset.univ : Finset (Fin N)) D
      (fun i => Finset.subset_univ (E i)) hCap (by omega)
  have hShorten : HeteroShortenable (q - 1) D
      (fun j S => v j (pullbackRealBundle D S))
      (fun j => u j j) (fun i => (w i).B) :=
    localWitness_shortenable w hEF D hDummyD (by omega)
  have hN' : N = n * (q - 1 + 1) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ q)] using hN
  exact hetero_finite_conversion_exists_balanced_ef11 D v
    (fun j => u j j) (fun i => (w i).B)
    (by omega) hN' hDlt hState hShorten

end FairDivision.BF
