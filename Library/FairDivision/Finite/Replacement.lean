import FairDivision.Definitions

/-!
# Replacing one item in a bracketed bundle

A finite step in the identical-valuation proof. If the values obtainable by
exactly one deletion bracket a threshold, replacing any one item by a fresh
item can preserve that property. No monotonicity is assumed of the valuation.
-/

set_option autoImplicit false

namespace FairDivision

/-- The values of two exact one-item deletions from `B` bracket `t`. -/
def BracketsOneDeletion {α : Type*} [DecidableEq α]
    (v : Finset α → ℝ) (B : Finset α) (t : ℝ) : Prop :=
  (∃ x ∈ B, v (B.erase x) ≤ t) ∧
    (∃ y ∈ B, t ≤ v (B.erase y))

/-- The replacement step used to absorb an unused dummy item. -/
theorem bracketsOneDeletion_replace {α : Type*} [DecidableEq α]
    (v : Finset α → ℝ) (B : Finset α) (t : ℝ)
    (hB : BracketsOneDeletion v B t) (e : α) (he : e ∉ B) :
    ∃ z ∈ B, BracketsOneDeletion v (insert e (B.erase z)) t := by
  obtain ⟨⟨y, hy, hlow⟩, ⟨x, hx, hhigh⟩⟩ := hB
  by_cases hxy : x = y
  · subst y
    refine ⟨x, hx, ?_⟩
    have hdelete : (insert e (B.erase x)).erase e = B.erase x :=
      Finset.erase_insert (fun heErase => he (Finset.mem_of_mem_erase heErase))
    exact ⟨⟨e, Finset.mem_insert_self _ _, by simpa only [hdelete] using hlow⟩,
      ⟨e, Finset.mem_insert_self _ _, by simpa only [hdelete] using hhigh⟩⟩
  · let C : Finset α := insert e ((B.erase x).erase y)
    by_cases hCt : v C ≤ t
    · refine ⟨x, hx, ?_⟩
      have hy' : y ∈ insert e (B.erase x) := by
        simp [hy, Ne.symm hxy]
      have he' : e ∈ insert e (B.erase x) := Finset.mem_insert_self _ _
      have hdelete_y : (insert e (B.erase x)).erase y = C := by
        have hey : e ≠ y := by
          intro hEq
          exact he (by rw [hEq]; exact hy)
        rw [Finset.erase_insert_of_ne hey]
      have hdelete_e : (insert e (B.erase x)).erase e = B.erase x :=
        Finset.erase_insert (fun heErase => he (Finset.mem_of_mem_erase heErase))
      exact ⟨⟨y, hy', by simpa only [hdelete_y] using hCt⟩,
        ⟨e, he', by simpa only [hdelete_e] using hhigh⟩⟩
    · refine ⟨y, hy, ?_⟩
      have hx' : x ∈ insert e (B.erase y) := by
        simp [hx, hxy, he]
      have he' : e ∈ insert e (B.erase y) := Finset.mem_insert_self _ _
      have hdelete_x : (insert e (B.erase y)).erase x = C := by
        have hex : e ≠ x := by
          intro hEq
          exact he (by rw [hEq]; exact hx)
        rw [Finset.erase_insert_of_ne hex]
        change insert e ((B.erase y).erase x) = insert e ((B.erase x).erase y)
        rw [Finset.erase_right_comm]
      have hdelete_e : (insert e (B.erase y)).erase e = B.erase y :=
        Finset.erase_insert (fun heErase => he (Finset.mem_of_mem_erase heErase))
      exact ⟨⟨e, he', by simpa only [hdelete_e] using hlow⟩,
        ⟨x, hx', by simpa only [hdelete_x] using le_of_lt (lt_of_not_ge hCt)⟩⟩

/-- Exact one-deletion brackets for every bundle imply the paper's optional
one-deletion common threshold. -/
theorem commonThreshold_of_bracketsOneDeletion {n m : ℕ}
    (v : Finset (Fin m) → ℝ) (A : Allocation n m) (t : ℝ)
    (h : ∀ i : Fin n, BracketsOneDeletion v (bundle A i) t) :
    HasCommonThreshold v A t := by
  intro i
  obtain ⟨⟨x, hx, hlow⟩, ⟨y, hy, hhigh⟩⟩ := h i
  constructor
  · refine ⟨{x}, ?_, ?_⟩
    · simp [CanDeleteOne, hx]
    · simpa only [Finset.sdiff_singleton_eq_erase] using hlow
  · refine ⟨{y}, ?_, ?_⟩
    · simp [CanDeleteOne, hy]
    · simpa only [Finset.sdiff_singleton_eq_erase] using hhigh

end FairDivision
