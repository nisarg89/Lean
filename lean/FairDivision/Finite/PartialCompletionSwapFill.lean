import FairDivision.Finite.PartialCompletionReplace

/-!
# The final BF dummy-completion move

An unused dummy cannot be inserted into a short bundle that already has a
dummy. The manuscript finds a full dummy-free donor, replaces a real item in
it by the unused dummy, and fills the short bundle with the removed real
item. This strictly decreases the number of short positions.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- Carry out one final-phase donor replacement and short-bundle filling
step, preserving the manuscript's partial-completion invariant. -/
theorem PartialCompletionState.swap_fill
    {α : Type*} [DecidableEq α]
    {n r : ℕ} {U D : Finset α} {v : Finset α → ℝ} {t : ℝ}
    {B : Fin n → Finset α}
    (h : PartialCompletionState n r U D v t B)
    (hD : D.card ≤ n)
    (i : Fin n) (hShort : (B i).card = r ∧ v (B i) = t)
    (e : α) (heD : e ∈ D)
    (he : e ∈ U \ Finset.univ.biUnion B)
    (hNoShortFree : ∀ j : Fin n, B j ∩ D = ∅ → (B j).card = r + 1) :
    ∃ B' : Fin n → Finset α,
      PartialCompletionState n r U D v t B' ∧
      (Finset.univ.filter (fun j : Fin n => (B' j).card = r)).card <
        (Finset.univ.filter (fun j : Fin n => (B j).card = r)).card := by
  classical
  obtain ⟨j, z, hz, hjDummyFree, hBracket⟩ :=
    h.exists_replacement_donor hD e heD he hNoShortFree
  have hjFull : (B j).card = r + 1 := hNoShortFree j hjDummyFree
  let B1 := Function.update B j (insert e ((B j).erase z))
  have hReplace : PartialCompletionState n r U D v t B1 ∧
      z ∈ U \ Finset.univ.biUnion B1 :=
    h.replace_full_donor j hjFull hjDummyFree e heD he z hz hBracket
  have hij : i ≠ j := by
    intro hEq
    subst j
    omega
  have hiDummy : (B i ∩ D).card = 1 := by
    have hiNonempty : (B i ∩ D).Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hiEmpty
      have hiFull := hNoShortFree i hiEmpty
      omega
    have hiPositive := Finset.card_pos.mpr hiNonempty
    have hiCap := h.2.2 i
    omega
  have hB1i : B1 i = B i := by
    simp [B1,Function.update,hij]
  have hShort1 : (B1 i).card = r ∧ v (B1 i) = t := by
    rw [hB1i]
    exact hShort
  have hzReal : z ∉ D := by
    intro hzD
    have hzx : z ∈ B j ∩ D := Finset.mem_inter.mpr ⟨hz, hzD⟩
    simpa [hjDummyFree] using hzx
  have hRecipientDummy : (insert z (B1 i) ∩ D).card = 1 := by
    rw [short_bundle_fill_real_dummy_count (B1 i) D z hzReal,hB1i]
    exact hiDummy
  have hCap : (insert z (B1 i) ∩ D).card ≤ 1 := hRecipientDummy.le
  let B2 := Function.update B1 i (insert z (B1 i))
  have hState2 : PartialCompletionState n r U D v t B2 :=
    hReplace.1.fill_unused i hShort1 z hReplace.2 hCap
  have hzNot : z ∉ B1 i := by
    intro hzi
    exact (Finset.mem_sdiff.mp hReplace.2).2
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hzi⟩)
  have hDecrease :
      (Finset.univ.filter (fun x : Fin n => (B2 x).card = r)).card <
        (Finset.univ.filter (fun x : Fin n => (B1 x).card = r)).card :=
    short_count_decreases_after_fill n r B1 i hShort1.1 z hzNot
  have hSame :
      (Finset.univ.filter (fun x : Fin n => (B1 x).card = r)) =
        (Finset.univ.filter (fun x : Fin n => (B x).card = r)) :=
    short_positions_after_donor_replace n r B j hjFull e
      (by
        intro heBj
        exact (Finset.mem_sdiff.mp he).2
          (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, heBj⟩)) z hz
  refine ⟨B2, hState2, ?_⟩
  rw [hSame] at hDecrease
  exact hDecrease

end FairDivision.Finite
