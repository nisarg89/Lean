import FairDivision.BF.HeterogeneousAdmissibility

/-!
# Admissibility of attained coordinatewise maxima

The manuscript fills a higher-dimensional face by taking one maximum per
agent over a compact boundary cap. Each maximum is attained, so at most one
boundary point per agent is needed. This lemma isolates the witness transfer
from the topology of the cap and from the choice of its maximum values.
-/

set_option autoImplicit false

namespace FairDivision.BF

/-- Every coordinatewise maximum of admissible vectors is admissible when
that coordinate's maximum is attained within the same stock. The selected
boundary points number at most the number of coordinates. -/
theorem isAdmissible_attained_coordinatewise_max
    {α : Type*} {n m q : ℕ} (dummy : Fin m)
    (v : Fin n → Finset (Fin m) → ℝ)
    (E : Finset (Fin m)) (K : Set α)
    (u : α → Fin n → ℝ)
    (hMax : ∀ j : Fin n, ∃ a ∈ K,
      ∀ b ∈ K, u b j ≤ u a j)
    (hAdm : ∀ a ∈ K, IsAdmissible q dummy v E (u a)) :
    IsAdmissible q dummy v E
      (fun j => u (Classical.choose (hMax j)) j) := by
  classical
  intro owner
  let a : α := Classical.choose (hMax owner)
  have ha : a ∈ K := (Classical.choose_spec (hMax owner)).1
  obtain ⟨w⟩ := hAdm a ha owner
  refine ⟨w.weaken ?_ ?_⟩
  · intro j
    exact (Classical.choose_spec (hMax j)).2 a ha
  · rfl

end FairDivision.BF
