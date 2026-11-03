import FairDivision.Finite.PartialCompletionState

/-!
# One filling step in the BF completion argument

An unused item can be inserted into a short exact-value bundle whenever
the dummy cap permits it. This preserves disjointness and every local
threshold witness. The manuscript uses this step first for real items and
then for dummy-free short bundles.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- Insert one unallocated item into a short bundle, preserving the
manuscript's simultaneous short/full invariant. -/
theorem PartialCompletionState.fill_unused {α : Type*} [DecidableEq α]
    {n r : ℕ} {U D : Finset α} {v : Finset α → ℝ} {t : ℝ}
    {B : Fin n → Finset α}
    (h : PartialCompletionState n r U D v t B)
    (i : Fin n) (hShort : (B i).card = r ∧ v (B i) = t)
    (e : α) (he : e ∈ U \ Finset.univ.biUnion B)
    (hCap : (insert e (B i) ∩ D).card ≤ 1) :
    PartialCompletionState n r U D v t
      (Function.update B i (insert e (B i))) := by
  classical
  have heU : e ∈ U := (Finset.mem_sdiff.mp he).1
  have heUnused (j : Fin n) : e ∉ B j := by
    intro heBj
    exact (Finset.mem_sdiff.mp he).2
      (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, heBj⟩)
  have hFill := short_bundle_fill v (B i) r t hShort.1 hShort.2
    e (heUnused i)
  refine ⟨?_, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simp [Function.update]
      constructor
      · exact Finset.insert_subset heU (h.1 i).1
      · exact Or.inr hFill
    · simpa [Function.update, hji] using h.1 j
  · intro j l hjl
    by_cases hji : j = i
    · subst j
      have hli : l ≠ i := Ne.symm hjl
      simp [Function.update, hli]
      exact ⟨heUnused l, h.2.1 i l hjl⟩
    · by_cases hli : l = i
      · subst l
        simp [Function.update, hji]
        exact ⟨heUnused j, h.2.1 j i hjl⟩
      · simpa [Function.update, hji, hli] using h.2.1 j l hjl
  · intro j
    by_cases hji : j = i
    · subst j
      simpa [Function.update] using hCap
    · simpa [Function.update, hji] using h.2.2 j

/-- Filling one short position removes exactly that position from the set of
short positions. This is the decreasing measure for the completion recursion. -/
theorem short_positions_after_fill {α : Type*} [DecidableEq α]
    (n r : ℕ) (B : Fin n → Finset α) (i : Fin n)
    (hShort : (B i).card = r) (e : α) (he : e ∉ B i) :
    (Finset.univ.filter
      (fun j : Fin n => (Function.update B i (insert e (B i)) j).card = r)) =
      (Finset.univ.filter (fun j : Fin n => (B j).card = r)).erase i := by
  classical
  have hFull : (insert e (B i)).card ≠ r := by
    have hCard : (insert e (B i)).card = r + 1 := by simp [he, hShort]
    omega
  ext j
  by_cases hji : j = i
  · subst j
    simp [Function.update, hFull]
  · simp [Function.update, hji, hji]

/-- One filling step strictly decreases the number of short positions. -/
theorem short_count_decreases_after_fill {α : Type*} [DecidableEq α]
    (n r : ℕ) (B : Fin n → Finset α) (i : Fin n)
    (hShort : (B i).card = r) (e : α) (he : e ∉ B i) :
    (Finset.univ.filter
      (fun j : Fin n => (Function.update B i (insert e (B i)) j).card = r)).card <
      (Finset.univ.filter (fun j : Fin n => (B j).card = r)).card := by
  classical
  rw [short_positions_after_fill n r B i hShort e he]
  have hi : i ∈ Finset.univ.filter (fun j : Fin n => (B j).card = r) := by
    simp [hShort]
  rw [Finset.card_erase_of_mem hi]
  have hpos : 0 < (Finset.univ.filter
      (fun j : Fin n => (B j).card = r)).card :=
    Finset.card_pos.mpr ⟨i, hi⟩
  omega

end FairDivision.Finite
