import FairDivision.Finite.SmallInstances
import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise

/-! A balanced allocation exists before any valuation or fairness condition is imposed. -/

set_option autoImplicit false

namespace FairDivision

/-- Equipartition the items and index its parts by agents. -/
theorem exists_balanced_allocation (n m : ℕ) (hn : 0 < n) :
    ∃ A : Allocation n m, IsBalanced A := by
  classical
  by_cases hm : n ≤ m
  · obtain ⟨P, hP, hparts⟩ :=
      Finpartition.exists_equipartition_card_eq
        (s := (Finset.univ : Finset (Fin m))) (n := n) (Nat.ne_of_gt hn) (by simpa using hm)
    let e : P.parts ≃ Fin n := Finset.equivFinOfCardEq hparts
    let A : Allocation n m := fun g => e ⟨P.part g, P.part_mem.mpr (Finset.mem_univ g)⟩
    have hbundle (i : Fin n) : bundle A i = (e.symm i).val := by
      ext g
      simp only [bundle, Finset.mem_filter, Finset.mem_univ, true_and]
      change e ⟨P.part g, P.part_mem.mpr (Finset.mem_univ g)⟩ = i ↔
        g ∈ (e.symm i).val
      rw [e.apply_eq_iff_eq_symm_apply]
      constructor
      · intro heq
        exact (P.part_eq_iff_mem (a := g) (e.symm i).property).mp
          (congrArg Subtype.val heq)
      · intro hg
        apply Subtype.ext
        exact (P.part_eq_iff_mem (a := g) (e.symm i).property).mpr hg
    refine ⟨A, ?_⟩
    intro i
    rw [hbundle]
    have hi : (e.symm i).val.card = m / n ∨
        (e.symm i).val.card = m / n + 1 := by
      simpa [hparts] using hP.card_parts_eq_average (e.symm i).property
    by_cases hmod : m % n = 0
    · have hlarge : (e.symm i).val.card ≠ m / n + 1 := by
        have hlarge_count := hP.card_large_parts_eq_mod
        rw [hparts] at hlarge_count
        simp only [Finset.card_fin, hmod] at hlarge_count
        have hempty := Finset.card_eq_zero.mp hlarge_count
        have hnot : (e.symm i).val ∉
            P.parts.filter (fun p => p.card = m / n + 1) := by
          rw [hempty]
          simp
        simpa [(e.symm i).property] using hnot
      left
      exact hi.resolve_right hlarge
    · rcases hi with hsmall | hlarge
      · exact Or.inl hsmall
      · exact Or.inr (by simpa [upperSize, hmod] using hlarge)
  · have hsmall : m ≤ n := Nat.le_of_lt (Nat.lt_of_not_ge hm)
    obtain ⟨A, _, hbalanced, _⟩ := identical_small hn hsmall (fun _ => (0 : ℝ))
    exact ⟨A, hbalanced⟩

end FairDivision
