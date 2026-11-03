import FairDivision.Finite.PartialCompletionFill
import FairDivision.Finite.PartialCompletionDonor

/-!
# Replacing a dummy in a full BF donor bundle

The manuscript's last completion phase first replaces an item of a full
bundle by an unused dummy. The removed real item becomes unallocated; the
ordinary short-bundle filling lemma can then insert it into a short bundle.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- Replacing a real item of a full dummy-free donor by an unused dummy
preserves the partial completion invariant and frees the removed item. -/
theorem PartialCompletionState.replace_full_donor
    {α : Type*} [DecidableEq α]
    {n r : ℕ} {U D : Finset α} {v : Finset α → ℝ} {t : ℝ}
    {B : Fin n → Finset α}
    (h : PartialCompletionState n r U D v t B)
    (j : Fin n) (hjFull : (B j).card = r + 1)
    (hjDummyFree : B j ∩ D = ∅)
    (e : α) (heD : e ∈ D)
    (he : e ∈ U \ Finset.univ.biUnion B)
    (z : α) (hz : z ∈ B j)
    (hBracket : FairDivision.BracketsOneDeletion v
      (insert e ((B j).erase z)) t) :
    let B' := Function.update B j (insert e ((B j).erase z))
    PartialCompletionState n r U D v t B' ∧
      z ∈ U \ Finset.univ.biUnion B' := by
  classical
  have heU : e ∈ U := (Finset.mem_sdiff.mp he).1
  have heUnused (i : Fin n) : e ∉ B i := by
    intro heBi
    exact (Finset.mem_sdiff.mp he).2
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, heBi⟩)
  have hzU : z ∈ U := (h.1 j).1 hz
  have hzReal : z ∉ D := by
    intro hzD
    have hzx : z ∈ B j ∩ D := Finset.mem_inter.mpr ⟨hz, hzD⟩
    simpa [hjDummyFree] using hzx
  have hEraseDummyFree : (B j).erase z ∩ D = ∅ := by
    ext x
    constructor
    · intro hx
      have hxBj : x ∈ B j :=
        (Finset.mem_erase.mp (Finset.mem_inter.mp hx).1).2
      have hxD : x ∈ D := (Finset.mem_inter.mp hx).2
      have hxx : x ∈ B j ∩ D := Finset.mem_inter.mpr ⟨hxBj, hxD⟩
      simpa [hjDummyFree] using hxx
    · simp
  have hNewCap : (insert e ((B j).erase z) ∩ D).card ≤ 1 :=
    (short_bundle_fill_dummy_count ((B j).erase z) D e heD hEraseDummyFree).le
  have hNewCard : (insert e ((B j).erase z)).card = r + 1 := by
    have heNotErase : e ∉ (B j).erase z :=
      fun heErase => heUnused j (Finset.erase_subset z (B j) heErase)
    calc
      (insert e ((B j).erase z)).card = ((B j).erase z).card + 1 :=
        Finset.card_insert_of_notMem heNotErase
      _ = (B j).card := Finset.card_erase_add_one hz
      _ = r + 1 := hjFull
  let B' := Function.update B j (insert e ((B j).erase z))
  have hState : PartialCompletionState n r U D v t B' := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      by_cases hij : i = j
      · subst i
        simp [B', Function.update]
        constructor
        · exact Finset.insert_subset heU
            ((Finset.erase_subset z (B j)).trans (h.1 j).1)
        · exact Or.inr ⟨hNewCard, hBracket⟩
      · simpa [B', Function.update, hij] using h.1 i
    · intro i l hil
      by_cases hij : i = j
      · subst i
        have hlj : l ≠ j := Ne.symm hil
        simp [B', Function.update, hlj]
        exact ⟨heUnused l,
          (h.2.1 j l hil).mono (Finset.erase_subset z (B j))
            (Finset.Subset.rfl)⟩
      · by_cases hlj : l = j
        · subst l
          simp [B', Function.update, hij]
          exact ⟨heUnused i,
            (h.2.1 i j hil).mono (Finset.Subset.rfl)
              (Finset.erase_subset z (B j))⟩
        · simpa [B', Function.update, hij, hlj] using h.2.1 i l hil
    · intro i
      by_cases hij : i = j
      · subst i
        simpa [B', Function.update] using hNewCap
      · simpa [B', Function.update, hij] using h.2.2 i
  have hzUnused : z ∈ U \ Finset.univ.biUnion B' := by
    apply Finset.mem_sdiff.mpr
    constructor
    · exact hzU
    · intro hzUnion
      obtain ⟨i, _, hzi⟩ := Finset.mem_biUnion.mp hzUnion
      by_cases hij : i = j
      · subst i
        have hze : z ≠ e := by
          intro hEq
          exact heUnused j (hEq ▸ hz)
        have hzNotErase : z ∉ (B j).erase z := by simp
        simp [B', Function.update, hze, hzNotErase] at hzi
      · have hziOld : z ∈ B i := by
          simpa [B', Function.update, hij] using hzi
        exact (Finset.disjoint_left.mp (h.2.1 j i (Ne.symm hij))) hz hziOld
  exact ⟨hState, hzUnused⟩

/-- Replacing an item inside an already full donor leaves the set of short
positions unchanged. -/
theorem short_positions_after_donor_replace
    {α : Type*} [DecidableEq α]
    (n r : ℕ) (B : Fin n → Finset α)
    (j : Fin n) (hjFull : (B j).card = r + 1)
    (e : α) (he : e ∉ B j) (z : α) (hz : z ∈ B j) :
    (Finset.univ.filter (fun i : Fin n =>
      (Function.update B j (insert e ((B j).erase z)) i).card = r)) =
      (Finset.univ.filter (fun i : Fin n => (B i).card = r)) := by
  classical
  have heErase : e ∉ (B j).erase z :=
    fun he' => he (Finset.erase_subset z (B j) he')
  have hNewCard : (insert e ((B j).erase z)).card = r + 1 := by
    calc
      (insert e ((B j).erase z)).card = ((B j).erase z).card + 1 :=
        Finset.card_insert_of_notMem heErase
      _ = (B j).card := Finset.card_erase_add_one hz
      _ = r + 1 := hjFull
  have hNotShort : (B j).card ≠ r := by omega
  have hNewNotShort : (insert e ((B j).erase z)).card ≠ r := by omega
  ext i
  by_cases hij : i = j
  · subst i
    simp [Function.update, hNotShort, hNewNotShort]
  · simp [Function.update, hij]

end FairDivision.Finite
