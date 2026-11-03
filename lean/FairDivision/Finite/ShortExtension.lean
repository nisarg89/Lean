import FairDivision.Finite.Replacement

/-!
# Extending an exact-value short bundle

Deleting the newly inserted item recovers the old value exactly, so the
extended bundle brackets the same threshold under one-item deletion.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- Adding any fresh item to a bundle of value `t` establishes an exact
one-deletion bracket, without a monotonicity assumption. -/
theorem bracketsOneDeletion_insert_of_eq {α : Type*} [DecidableEq α]
    (v : Finset α → ℝ) (B : Finset α) (t : ℝ)
    (hB : v B = t) (e : α) (he : e ∉ B) :
    FairDivision.BracketsOneDeletion v (insert e B) t := by
  have hErase : (insert e B).erase e = B := Finset.erase_insert he
  constructor
  · exact ⟨e, Finset.mem_insert_self _ _, by rw [hErase, hB]⟩
  · exact ⟨e, Finset.mem_insert_self _ _, by rw [hErase, hB]⟩

end FairDivision.Finite
