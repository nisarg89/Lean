import Mathlib

/-!
# Allocating disjoint finite reserves of prescribed sizes

This elementary lemma is used to choose disjoint labeled dummy-item reserves
from an aggregate cardinality bound in the auxiliary lottery complex.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- If the requested reserve sizes fit in a finite stock, give each position
a disjoint subset of exactly its requested size. -/
theorem exists_disjoint_reserves {ι α : Type*}
    [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (D : Finset α) (cap : ι → ℕ)
    (hfit : (∑ i ∈ I, cap i) ≤ D.card) :
    ∃ R : ι → Finset α,
      (∀ i ∈ I, R i ⊆ D ∧ (R i).card = cap i) ∧
      ((I : Set ι).PairwiseDisjoint R) := by
  induction I using Finset.induction_on generalizing D with
  | empty =>
      refine ⟨fun _ => ∅, ?_, ?_⟩
      · simp
      · simp
  | @insert a I ha ih =>
      classical
      have hsplit : cap a + (∑ i ∈ I, cap i) ≤ D.card := by
        simpa [Finset.sum_insert ha] using hfit
      have hcap : cap a ≤ D.card := by omega
      obtain ⟨A, hAD, hAcard⟩ := D.exists_subset_card_eq hcap
      have hDcard : (D \ A).card = D.card - cap a := by
        rw [Finset.card_sdiff_of_subset hAD, hAcard]
      have hrest : (∑ i ∈ I, cap i) ≤ (D \ A).card := by
        omega
      obtain ⟨R, hR, hPair⟩ := ih (D \ A) hrest
      let R' : ι → Finset α := fun i => if i = a then A else R i
      refine ⟨R', ?_, ?_⟩
      · intro i hi
        by_cases hia : i = a
        · subst i
          simpa [R'] using And.intro hAD hAcard
        · have hiI : i ∈ I := (Finset.mem_insert.mp hi).resolve_left hia
          have hRi := hR i hiI
          have hRD : R i ⊆ D := hRi.1.trans (Finset.sdiff_subset)
          simpa [R', hia] using And.intro hRD hRi.2
      · intro i hi j hj hij
        have hia : i = a ∨ i ∈ I := Finset.mem_insert.mp hi
        have hja : j = a ∨ j ∈ I := Finset.mem_insert.mp hj
        rcases hia with rfl | hiI
        · rcases hja with rfl | hjI
          · exact False.elim (hij rfl)
          · have hja : j ≠ i := by
              intro h
              subst j
              exact ha hjI
            have hRj : R j ⊆ D \ A := (hR j hjI).1
            have hdisj : Disjoint A (R j) := by
              apply Finset.disjoint_left.mpr
              intro x hxA hxRj
              exact (Finset.mem_sdiff.mp (hRj hxRj)).2 hxA
            change Disjoint (R' i) (R' j)
            simpa [R', hja] using hdisj
        · rcases hja with rfl | hjI
          · have hia : i ≠ j := by
              intro h
              subst i
              exact ha hiI
            have hRi : R i ⊆ D \ A := (hR i hiI).1
            have hdisj : Disjoint (R i) A := by
              apply Finset.disjoint_left.mpr
              intro x hxRi hxA
              exact (Finset.mem_sdiff.mp (hRi hxRi)).2 hxA
            change Disjoint (R' i) (R' j)
            simpa [R', hia] using hdisj
          · have hia : i ≠ a := by
              intro h
              subst i
              exact ha hiI
            have hja : j ≠ a := by
              intro h
              subst j
              exact ha hjI
            change Disjoint (R' i) (R' j)
            simpa [R', hia, hja] using hPair hiI hjI hij

end FairDivision.Finite
