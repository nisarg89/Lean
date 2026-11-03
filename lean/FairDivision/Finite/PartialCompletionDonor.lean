import FairDivision.Finite.PartialCompletionState
import FairDivision.Finite.Replacement

/-!
# Replacement donor in the final BF filling phase

When an unused dummy remains but every dummy-free short bundle has been
filled, the manuscript takes a full dummy-free donor. The one-item
replacement lemma exchanges one of its real items for the unused dummy
while preserving the threshold bracket.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- Find the full dummy-free donor and a replaceable item for the final
phase of the manuscript's completion. -/
theorem PartialCompletionState.exists_replacement_donor
    {α : Type*} [DecidableEq α]
    {n r : ℕ} {U D : Finset α} {v : Finset α → ℝ} {t : ℝ}
    {B : Fin n → Finset α}
    (h : PartialCompletionState n r U D v t B)
    (hD : D.card ≤ n)
    (e : α) (heD : e ∈ D)
    (heUnused : e ∈ U \ Finset.univ.biUnion B)
    (hNoShortFree : ∀ i : Fin n, B i ∩ D = ∅ → (B i).card = r + 1) :
    ∃ j : Fin n, ∃ z ∈ B j,
      B j ∩ D = ∅ ∧
      FairDivision.BracketsOneDeletion v
        (insert e ((B j).erase z)) t := by
  classical
  have heNot (i : Fin n) : e ∉ B i := by
    intro heBi
    exact (Finset.mem_sdiff.mp heUnused).2
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, heBi⟩)
  obtain ⟨j, hjD, hjFull⟩ := exists_full_dummy_free_position
    n r D B hD h.2.1 e heD heNot hNoShortFree
  have hjBracket : FairDivision.BracketsOneDeletion v (B j) t := by
    rcases (h.1 j).2 with hShort | hFull
    · omega
    · exact hFull.2
  obtain ⟨z, hz, hReplace⟩ :=
    FairDivision.bracketsOneDeletion_replace v (B j) t
      hjBracket e (heNot j)
  exact ⟨j, z, hz, hjD, hReplace⟩

end FairDivision.Finite
