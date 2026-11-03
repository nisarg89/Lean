import FairDivision.BF.HeterogeneousWitnessComparison

/-!
# BF Section 5: observer and owner deletion brackets

A selected virtual-valuation bundle supplies one optional deletion for every
observer's lower comparison and another for its owner's upper comparison.
The witnesses can differ by observer. Appending an unused real item to a
short selected bundle preserves these brackets by deleting that item.
-/

set_option autoImplicit false

namespace FairDivision.BF

/-- The comparisons that a selected position bundle must retain through the
heterogeneous allocation conversion. -/
def HeteroBrackets {n m : ℕ}
    (v : Fin n → Finset (Fin m) → ℝ) (τ : Fin n → ℝ)
    (owner : Fin n) (B : Finset (Fin m)) : Prop :=
  (∀ observer : Fin n,
    ∃ D : Finset (Fin m),
      CanDeleteOne D B ∧ v observer (B \ D) ≤ τ observer) ∧
  (∃ D : Finset (Fin m),
    CanDeleteOne D B ∧ τ owner ≤ v owner (B \ D))

/-- Every `(q-1)`-item subset of a short or full selected bundle is
obtainable by deleting at most one item. -/
theorem witnessSubset_oneDeletion
    {m q : ℕ} {B F : Finset (Fin m)}
    (hFB : F ⊆ B) (hF : F.card = q - 1)
    (hB : B.card = q - 1 ∨ B.card = q) :
    CanDeleteOne (B \ F) B ∧ B \ (B \ F) = F := by
  have hCard : (B \ F).card = B.card - F.card :=
    Finset.card_sdiff_of_subset hFB
  constructor
  · constructor
    · exact Finset.sdiff_subset
    · rcases hB with hShort | hFull <;> omega
  · exact Finset.sdiff_sdiff_eq_self hFB

/-- Selected owner witnesses give the actual optional-deletion brackets
used in the manuscript's heterogeneous completion. -/
theorem selectedWitness_brackets
    {n m q : ℕ} {dummy : Fin m}
    {v : Fin n → Finset (Fin m) → ℝ}
    {E : Fin n → Finset (Fin m)}
    {u : Fin n → Fin n → ℝ}
    (w : ∀ s : Fin n, OwnerWitness q dummy v (E s) (u s) s)
    (hEF : ∀ i j : Fin n, u j i ≤ u i i)
    (i : Fin n) :
    HeteroBrackets v (fun j => u j j) i (w i).B := by
  constructor
  · intro j
    let D := (w i).B \ (w i).lowerSet
    have hDelete := witnessSubset_oneDeletion
      (w i).lower_subset (w i).lower_size (w i).size
    refine ⟨D, hDelete.1, ?_⟩
    change v j ((w i).B \ D) ≤ u j j
    rw [hDelete.2]
    exact ((w i).lower_bound j).trans (hEF j i)
  · let D := (w i).B \ (w i).upperSet
    have hDelete := witnessSubset_oneDeletion
      (w i).upper_subset (w i).upper_size (w i).size
    refine ⟨D, hDelete.1, ?_⟩
    change u i i ≤ v i ((w i).B \ D)
    rw [hDelete.2]
    exact (w i).owner_bound

/-- Inserting a fresh item into a short bundle preserves its observer and
owner comparisons: every comparison deletes the inserted item. -/
theorem HeteroBrackets.insert_of_short
    {n m : ℕ} {v : Fin n → Finset (Fin m) → ℝ}
    {τ : Fin n → ℝ} {owner : Fin n}
    {B : Finset (Fin m)}
    (hLower : ∀ j : Fin n, v j B ≤ τ j)
    (hUpper : τ owner ≤ v owner B)
    (e : Fin m) (he : e ∉ B) :
    HeteroBrackets v τ owner (insert e B) := by
  have hDelete : CanDeleteOne ({e} : Finset (Fin m)) (insert e B) := by
    constructor
    · simp
    · simp
  have hRemove : insert e B \ {e} = B := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.erase_insert he]
  constructor
  · intro j
    exact ⟨{e}, hDelete, by simpa only [hRemove] using hLower j⟩
  · exact ⟨{e}, hDelete, by simpa only [hRemove] using hUpper⟩

/-- A short bundle with direct value bounds has deletion brackets using
empty deletions. This is the certificate retained when a newly filled full
bundle is shortened again. -/
theorem HeteroBrackets.of_short_values
    {n m : ℕ} {v : Fin n → Finset (Fin m) → ℝ}
    {τ : Fin n → ℝ} {owner : Fin n}
    {B : Finset (Fin m)}
    (hLower : ∀ j : Fin n, v j B ≤ τ j)
    (hUpper : τ owner ≤ v owner B) :
    HeteroBrackets v τ owner B := by
  constructor
  · intro j
    refine ⟨∅, ?_, ?_⟩
    · simp [CanDeleteOne]
    · simpa using hLower j
  · refine ⟨∅, ?_, ?_⟩
    · simp [CanDeleteOne]
    · simpa using hUpper

/-- The short selected bundle itself satisfies every observer's lower bound
and its owner's upper bound. -/
theorem selectedWitness_short_values
    {n m q : ℕ} {dummy : Fin m}
    {v : Fin n → Finset (Fin m) → ℝ}
    {E : Fin n → Finset (Fin m)}
    {u : Fin n → Fin n → ℝ}
    (w : ∀ s : Fin n, OwnerWitness q dummy v (E s) (u s) s)
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


/-- An unused real item can fill a selected short bundle while retaining
all of its heterogeneous threshold comparisons. -/
theorem selectedWitness_short_fill_brackets
    {n m q : ℕ} {dummy : Fin m}
    {v : Fin n → Finset (Fin m) → ℝ}
    {E : Fin n → Finset (Fin m)}
    {u : Fin n → Fin n → ℝ}
    (w : ∀ s : Fin n, OwnerWitness q dummy v (E s) (u s) s)
    (hEF : ∀ i j : Fin n, u j i ≤ u i i)
    (i : Fin n) (hi : (w i).B.card = q - 1)
    (e : Fin m) (he : e ∉ (w i).B) :
    HeteroBrackets v (fun j => u j j) i (insert e (w i).B) := by
  obtain ⟨hLower, hUpper⟩ := selectedWitness_short_values w hEF i hi
  exact HeteroBrackets.insert_of_short hLower hUpper e he


/-- A selected full bundle with no dummy has the manuscript's certified
shortening. Every observer keeps a lower optional-deletion comparison, and
the owner keeps an upper one. -/
theorem selectedWitness_dummyFree_shorten
    {n m q : ℕ} {dummy : Fin m}
    {v : Fin n → Finset (Fin m) → ℝ}
    {E : Fin n → Finset (Fin m)}
    {u : Fin n → Fin n → ℝ}
    (w : ∀ s : Fin n, OwnerWitness q dummy v (E s) (u s) s)
    (hEF : ∀ i j : Fin n, u j i ≤ u i i)
    (i : Fin n) (hFull : (w i).B.card = q)
    (hNoDummy : dummy ∉ (w i).B) :
    ∃ C : Finset (Fin m),
      C ⊆ (w i).B ∧ C.card = q - 1 ∧
      HeteroBrackets v (fun j => u j j) i C := by
  obtain ⟨C, hCB, hCard, hLower, hUpper⟩ :=
    (w i).shortening hFull hNoDummy
  refine ⟨C, hCB, hCard, ?_⟩
  constructor
  · intro j
    obtain ⟨D, hD, hVal⟩ := hLower j
    exact ⟨D, hD, hVal.trans (hEF j i)⟩
  · exact hUpper

end FairDivision.BF
