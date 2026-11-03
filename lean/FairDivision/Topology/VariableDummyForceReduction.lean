import FairDivision.Topology.VariableDummyRetractions
import FairDivision.Topology.VariableDummyInductionArithmetic
import FairDivision.Topology.VariableDummyVertexBuild

/-!
# Deleting a forced real item

The manuscript's item-cover branch forces one item `e` into position `a`
and then deletes it. The following vertex-level constructions encode this
reduction and its inverse while retaining the same ambient `Fin m` item
type. The stock restriction excludes `e` from all reduced real bundles.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- The dummy counts of one auxiliary vertex fit the total dummy stock. -/
theorem variableProfile_dummy_total_le {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (p : VariableUnlabeledVertex k m D r c) :
    (∑ i : Fin k, (p.1 i).2) ≤ D.card := by
  classical
  have h := ((variableFace_iff
    ({p} : Finset (VariableUnlabeledVertex k m D r c))).1
      (variableUnlabeled_singleton p)).2
  simpa [variableDummyMax] using h

/-- Delete the fixed real item from one position of a vertex. -/
theorem exists_variableForcedReducedVertex {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (a : Fin k) (hra : 0 < r a)
    (p : VariableUnlabeledVertex k m D r c)
    (he : e ∈ (p.1 a).1) :
    ∃ q : VariableUnlabeledVertex k m D
      (variableDecreasedRequirement r a) c,
      ∀ i : Fin k, q.1 i =
        (if i = a then (p.1 i).1.erase e else (p.1 i).1,
          (p.1 i).2) := by
  let F (i : Fin k) : Finset (Fin m) :=
    if i = a then (p.1 i).1.erase e else (p.1 i).1
  have hSub (i : Fin k) : F i ⊆ (p.1 i).1 := by
    by_cases hi : i = a
    · subst i
      simpa [F] using Finset.erase_subset e (p.1 a).1
    · simp [F, hi]
  have hCard (i : Fin k) : (F i).card + (p.1 i).2 =
      variableDecreasedRequirement r a i := by
    by_cases hi : i = a
    · subst i
      have h := variableProfile_card p a
      have heCard := Finset.card_erase_of_mem he
      have hPos : 0 < (p.1 a).1.card :=
        Finset.card_pos.mpr ⟨e, he⟩
      simp only [F, ↓reduceIte, variableDecreasedRequirement_at]
      omega
    · simpa [F, hi] using variableProfile_card p i
  have hExists : ∃ q : VariableUnlabeledVertex k m D
      (variableDecreasedRequirement r a) c,
      ∀ i : Fin k, q.1 i = (F i, (p.1 i).2) := by
    apply exists_variable_vertex_of_profile F (fun i => (p.1 i).2)
    · intro i
      exact (variableProfile_real_disjoint_dummy p i).mono_left (hSub i)
    · intro i j hij
      exact (variableProfile_real_pairwise p i j hij).mono
        (hSub i) (hSub j)
    · exact hCard
    · intro i
      exact variableProfile_dummy_le_cap p i
    · exact variableProfile_dummy_total_le p
  simpa [F] using hExists

/-- Add `e` to the selected position of a reduced vertex whose real
bundles all avoid `e`. -/
theorem exists_variableForcedLiftVertex {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (heD : e ∉ D)
    (a : Fin k) (hra : 0 < r a)
    (q : VariableUnlabeledVertex k m D
      (variableDecreasedRequirement r a) c)
    (heAbsent : ∀ i : Fin k, e ∉ (q.1 i).1) :
    ∃ p : VariableUnlabeledVertex k m D r c,
      ∀ i : Fin k, p.1 i =
        (if i = a then insert e (q.1 i).1 else (q.1 i).1,
          (q.1 i).2) := by
  let F (i : Fin k) : Finset (Fin m) :=
    if i = a then insert e (q.1 i).1 else (q.1 i).1
  have hCard (i : Fin k) : (F i).card + (q.1 i).2 = r i := by
    by_cases hi : i = a
    · subst i
      have h := variableProfile_card q a
      have heCard := Finset.card_insert_of_notMem (heAbsent a)
      simp only [F, ↓reduceIte, variableDecreasedRequirement_at] at h ⊢
      omega
    · have h := variableProfile_card q i
      simpa [F, hi] using h
  have hExists : ∃ p : VariableUnlabeledVertex k m D r c,
      ∀ i : Fin k, p.1 i = (F i, (q.1 i).2) := by
    apply exists_variable_vertex_of_profile F (fun i => (q.1 i).2)
    · intro i
      by_cases hi : i = a
      · subst i
        apply Finset.disjoint_left.mpr
        intro g hg hD
        rcases Finset.mem_insert.mp (by simpa [F] using hg) with hge | hgq
        · exact heD (hge ▸ hD)
        · exact (Finset.disjoint_left.mp
            (variableProfile_real_disjoint_dummy q a)) hgq hD
      · simpa [F, hi] using variableProfile_real_disjoint_dummy q i
    · intro i j hij
      apply Finset.disjoint_left.mpr
      intro g hgi hgj
      by_cases hi : i = a
      · subst i
        have hj : j ≠ a := Ne.symm hij
        rcases Finset.mem_insert.mp (by simpa [F] using hgi) with hge | hgq
        · exact heAbsent j (hge ▸ (by simpa [F, hj] using hgj))
        · exact (Finset.disjoint_left.mp
            (variableProfile_real_pairwise q a j hij)) hgq
              (by simpa [F, hj] using hgj)
      · by_cases hj : j = a
        · subst j
          rcases Finset.mem_insert.mp (by simpa [F] using hgj) with hge | hgq
          · exact heAbsent i (hge ▸ (by simpa [F, hi] using hgi))
          · exact (Finset.disjoint_left.mp
              (variableProfile_real_pairwise q i a hij))
                (by simpa [F, hi] using hgi) hgq
        · exact (Finset.disjoint_left.mp
            (variableProfile_real_pairwise q i j hij))
              (by simpa [F, hi] using hgi)
              (by simpa [F, hj] using hgj)
    · exact hCard
    · intro i
      exact variableProfile_dummy_le_cap q i
    · exact variableProfile_dummy_total_le q
  simpa [F] using hExists


/-- Choose the reduced vertex obtained by deleting the forced item. -/
noncomputable def variableForcedReducedVertex {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (a : Fin k) (hra : 0 < r a)
    (p : VariableUnlabeledVertex k m D r c)
    (he : e ∈ (p.1 a).1) :
    VariableUnlabeledVertex k m D
      (variableDecreasedRequirement r a) c :=
  Classical.choose (exists_variableForcedReducedVertex e a hra p he)

/-- The selected reduced vertex preserves dummy counts and deletes `e`
only from position `a`. -/
theorem variableForcedReducedVertex_spec {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (a : Fin k) (hra : 0 < r a)
    (p : VariableUnlabeledVertex k m D r c)
    (he : e ∈ (p.1 a).1) (i : Fin k) :
    (variableForcedReducedVertex e a hra p he).1 i =
      (if i = a then (p.1 i).1.erase e else (p.1 i).1,
        (p.1 i).2) :=
  Classical.choose_spec (exists_variableForcedReducedVertex
    e a hra p he) i

/-- Choose the inverse vertex obtained by inserting the absent item. -/
noncomputable def variableForcedLiftVertex {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (heD : e ∉ D)
    (a : Fin k) (hra : 0 < r a)
    (q : VariableUnlabeledVertex k m D
      (variableDecreasedRequirement r a) c)
    (heAbsent : ∀ i : Fin k, e ∉ (q.1 i).1) :
    VariableUnlabeledVertex k m D r c :=
  Classical.choose (exists_variableForcedLiftVertex
    e heD a hra q heAbsent)

/-- The selected inverse vertex preserves dummy counts and inserts `e`
only at position `a`. -/
theorem variableForcedLiftVertex_spec {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (heD : e ∉ D)
    (a : Fin k) (hra : 0 < r a)
    (q : VariableUnlabeledVertex k m D
      (variableDecreasedRequirement r a) c)
    (heAbsent : ∀ i : Fin k, e ∉ (q.1 i).1)
    (i : Fin k) :
    (variableForcedLiftVertex e heD a hra q heAbsent).1 i =
      (if i = a then insert e (q.1 i).1 else (q.1 i).1,
        (q.1 i).2) :=
  Classical.choose_spec (exists_variableForcedLiftVertex
    e heD a hra q heAbsent) i

end FairDivision.Topology
