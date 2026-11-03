import FairDivision.Finite.ExchangeBracket
import FairDivision.Finite.Replacement

/-!
# Completing a threshold-crossing exchange to a full bundle

The union of adjacent short bundles in an exchange path has one more item.
Deleting the two exchanged items recovers values on opposite sides of the
common threshold.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- If supported equal-size bundles in one pool have values on opposite sides
of `t`, a full bundle in that pool brackets `t` under exact one-item deletion. -/
theorem exists_full_bracket_bundle {α : Type*} [DecidableEq α]
    (U B C : Finset α) (r : ℕ) (v : Finset α → ℝ) (t : ℝ)
    (hBU : B ⊆ U) (hCU : C ⊆ U)
    (hBcard : B.card = r) (hCcard : C.card = r)
    (hLow : v B < t) (hHigh : t ≤ v C) :
    ∃ H : Finset α,
      H ⊆ U ∧ H.card = r + 1 ∧
        FairDivision.BracketsOneDeletion v H t := by
  classical
  obtain ⟨F, a, b, hFU, hFcard, haF, hbUF, hFt, hGt⟩ :=
    exists_exchange_bracket U B C r v t
      hBU hCU hBcard hCcard hLow hHigh
  have hbU : b ∈ U := (Finset.mem_sdiff.mp hbUF).1
  have hbF : b ∉ F := (Finset.mem_sdiff.mp hbUF).2
  have hba : b ≠ a := by
    intro heq
    exact hbF (by simpa [heq] using haF)
  refine ⟨insert b F, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hbU
    · exact hFU hx
  · rw [Finset.card_insert_of_notMem hbF, hFcard]
  · constructor
    · refine ⟨b, Finset.mem_insert_self _ _, ?_⟩
      simpa only [Finset.erase_insert hbF] using le_of_lt hFt
    · refine ⟨a, Finset.mem_insert_of_mem haF, ?_⟩
      rwa [Finset.erase_insert_of_ne hba]

end FairDivision.Finite
