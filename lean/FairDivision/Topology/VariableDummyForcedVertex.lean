import FairDivision.Topology.VariableDummySaturation
import FairDivision.Topology.VariableDummyCover

/-!
# The vertex operation that forces a real item to one position

On an item-restricted cover member, a vertex not yet assigning `e` to the
permitted position can insert it there. If the position uses a dummy, its
dummy count drops by one; otherwise one real item is replaced. The operation
only shrinks old real bundles apart from inserting `e`, and never increases
dummy counts.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Total dummy demand of one variable-size profile fits in the stock. -/
theorem variableProfile_dummy_budget {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (p : VariableUnlabeledVertex k m D r c) :
    (∑ i : Fin k, (p.1 i).2) ≤ D.card := by
  classical
  have h := ((variableFace_iff ({p} :
    Finset (VariableUnlabeledVertex k m D r c))).1
      (variableUnlabeled_singleton p)).2
  simpa [variableDummyMax] using h

/-- Change one position's profile while keeping the others fixed. The new
real part may include one prescribed item that is absent from every other
position. -/
private theorem exists_variable_vertex_replace_position {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (p : VariableUnlabeledVertex k m D r c)
    (e : Fin m) (a : Fin k)
    (hOnly : ∀ j : Fin k, j ≠ a → e ∉ (p.1 j).1)
    (F : Finset (Fin m)) (d : ℕ)
    (hFsub : F ⊆ insert e (p.1 a).1)
    (hFdisj : Disjoint F D)
    (hFcard : F.card + d = r a)
    (hdCap : d ≤ c a)
    (hdOld : d ≤ (p.1 a).2) :
    ∃ q : VariableUnlabeledVertex k m D r c,
      q.1 a = (F, d) ∧
      ∀ j : Fin k, j ≠ a → q.1 j = p.1 j := by
  classical
  let FF (i : Fin k) : Finset (Fin m) :=
    if i = a then F else (p.1 i).1
  let dd (i : Fin k) : ℕ :=
    if i = a then d else (p.1 i).2
  have hFD (i : Fin k) : Disjoint (FF i) D := by
    by_cases hi : i = a
    · simpa [FF, hi] using hFdisj
    · simpa [FF, hi] using variableProfile_real_disjoint_dummy p i
  have hFPair (i j : Fin k) (hij : i ≠ j) :
      Disjoint (FF i) (FF j) := by
    by_cases hi : i = a
    · subst i
      have hj : j ≠ a := Ne.symm hij
      simp only [FF, if_pos rfl, if_neg hj]
      apply Finset.disjoint_left.mpr
      intro g hgF hgj
      rcases Finset.mem_insert.mp (hFsub hgF) with hge | hga
      · subst g
        exact hOnly j hj hgj
      · exact (Finset.disjoint_left.mp
          (variableProfile_real_pairwise p a j hij)) hga hgj
    · by_cases hj : j = a
      · subst j
        simp only [FF, if_neg hi, if_pos rfl]
        apply Finset.disjoint_left.mpr
        intro g hgi hgF
        rcases Finset.mem_insert.mp (hFsub hgF) with hge | hga
        · subst g
          exact hOnly i hi hgi
        · exact (Finset.disjoint_left.mp
            (variableProfile_real_pairwise p i a hij)) hgi hga
      · simpa [FF, hi, hj] using variableProfile_real_pairwise p i j hij
  have hCard (i : Fin k) : (FF i).card + dd i = r i := by
    by_cases hi : i = a
    · simpa [FF, dd, hi] using hFcard
    · simpa [FF, dd, hi] using variableProfile_card p i
  have hCap (i : Fin k) : dd i ≤ c i := by
    by_cases hi : i = a
    · simpa [dd, hi] using hdCap
    · simpa [dd, hi] using variableProfile_dummy_le_cap p i
  have hBudget : (∑ i : Fin k, dd i) ≤ D.card := by
    calc
      (∑ i : Fin k, dd i) ≤ ∑ i : Fin k, (p.1 i).2 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i = a
        · simpa [dd, hi] using hdOld
        · simp [dd, hi]
      _ ≤ D.card := variableProfile_dummy_budget p
  obtain ⟨q, hq⟩ := exists_variable_vertex_of_profile
    FF dd hFD hFPair hCard hCap hBudget
  refine ⟨q, ?_, ?_⟩
  · simpa [FF, dd] using hq a
  · intro j hj
    simpa [FF, dd, hj] using hq j

/-- Force an absent real item into the permitted position, replacing a dummy
when possible and otherwise replacing one real item. -/
theorem exists_variable_vertex_forcing {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (p : VariableUnlabeledVertex k m D r c)
    (e : Fin m) (heD : e ∉ D) (a : Fin k) (hra : 0 < r a)
    (hOnly : ∀ j : Fin k, j ≠ a → e ∉ (p.1 j).1)
    (heA : e ∉ (p.1 a).1) :
    ∃ q : VariableUnlabeledVertex k m D r c,
      e ∈ (q.1 a).1 ∧
      (∀ j : Fin k,
        (q.1 j).1 ⊆
          if j = a then insert e (p.1 j).1 else (p.1 j).1) ∧
      (∀ j : Fin k, (q.1 j).2 ≤ (p.1 j).2) := by
  classical
  by_cases hd : 0 < (p.1 a).2
  · let F := insert e (p.1 a).1
    let d := (p.1 a).2 - 1
    have hFdisj : Disjoint F D := by
      apply Finset.disjoint_left.mpr
      intro g hg hgD
      rcases Finset.mem_insert.mp hg with hge | hgp
      · subst g
        exact heD hgD
      · exact (Finset.disjoint_left.mp
          (variableProfile_real_disjoint_dummy p a)) hgp hgD
    have hFcard : F.card + d = r a := by
      have hOld := variableProfile_card p a
      have hInsert : F.card = (p.1 a).1.card + 1 := by
        exact Finset.card_insert_of_notMem heA
      dsimp [d]
      omega
    obtain ⟨q, hqa, hqOther⟩ :=
      exists_variable_vertex_replace_position p e a hOnly F d
        (by simp [F]) hFdisj hFcard
        (Nat.sub_le _ _ |>.trans (variableProfile_dummy_le_cap p a))
        (Nat.sub_le _ _)
    refine ⟨q, ?_, ?_, ?_⟩
    · rw [hqa]
      exact Finset.mem_insert_self _ _
    · intro j
      by_cases hj : j = a
      · subst j
        rw [hqa]
        simp [F]
      · rw [hqOther j hj]
        simp [hj]
    · intro j
      by_cases hj : j = a
      · subst j
        rw [hqa]
        exact Nat.sub_le _ _
      · rw [hqOther j hj]
  · have hd0 : (p.1 a).2 = 0 := Nat.eq_zero_of_not_pos hd
    have hRealPos : 0 < (p.1 a).1.card := by
      have hOld := variableProfile_card p a
      omega
    let z := (p.1 a).1.min' (Finset.card_pos.mp hRealPos)
    have hz : z ∈ (p.1 a).1 := Finset.min'_mem _ _
    let F := insert e ((p.1 a).1.erase z)
    have hFsub : F ⊆ insert e (p.1 a).1 := by
      intro g hg
      rcases Finset.mem_insert.mp hg with hge | hgerase
      · exact hge ▸ Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem
          (Finset.erase_subset _ _ hgerase)
    have hFdisj : Disjoint F D := by
      apply Finset.disjoint_left.mpr
      intro g hg hgD
      rcases Finset.mem_insert.mp hg with hge | hgerase
      · subst g
        exact heD hgD
      · exact (Finset.disjoint_left.mp
          (variableProfile_real_disjoint_dummy p a))
          (Finset.erase_subset _ _ hgerase) hgD
    have hFcard : F.card + (p.1 a).2 = r a := by
      have hOld := variableProfile_card p a
      have heErase : e ∉ (p.1 a).1.erase z :=
        fun he => heA (Finset.erase_subset _ _ he)
      have hInsert : F.card = ((p.1 a).1.erase z).card + 1 :=
        Finset.card_insert_of_notMem heErase
      have hErase := Finset.card_erase_add_one hz
      omega
    obtain ⟨q, hqa, hqOther⟩ :=
      exists_variable_vertex_replace_position p e a hOnly F (p.1 a).2
        hFsub hFdisj hFcard (variableProfile_dummy_le_cap p a) le_rfl
    refine ⟨q, ?_, ?_, ?_⟩
    · rw [hqa]
      exact Finset.mem_insert_self _ _
    · intro j
      by_cases hj : j = a
      · subst j
        rw [hqa]
        simpa using hFsub
      · rw [hqOther j hj]
        simp [hj]
    · intro j
      by_cases hj : j = a
      · subst j
        rw [hqa]
      · rw [hqOther j hj]

end FairDivision.Topology
