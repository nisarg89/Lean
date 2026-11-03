import FairDivision.Finite.PartialCompletionSwapFill

/-!
# Completing the BF partial bundles

The manuscript's three phases are implemented by well-founded induction on
the number of short bundles. Real unused items fill arbitrary short bundles;
unused dummies fill dummy-free short bundles; the remaining case uses the
full dummy-free replacement donor. Every step decreases the short count.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- A family of disjoint short/full bundles satisfying the common threshold
can be completed to full bundles, provided the dummy stock has at most one
item per position. -/
theorem complete_partial_bundles {α : Type*} [DecidableEq α]
    (n r : ℕ) (U D : Finset α) (v : Finset α → ℝ) (t : ℝ)
    (hTotal : U.card = n * (r + 1)) (hD : D.card ≤ n)
    (B : Fin n → Finset α)
    (hB : PartialCompletionState n r U D v t B) :
    ∃ A : Fin n → Finset α,
      PartialCompletionState n r U D v t A ∧
      (∀ i : Fin n, (A i).card = r + 1) ∧
      Finset.univ.biUnion A = U := by
  classical
  let shortCount (C : Fin n → Finset α) : ℕ :=
    (Finset.univ.filter (fun i : Fin n => (C i).card = r)).card
  let P : ℕ → Prop := fun s =>
    ∀ C : Fin n → Finset α,
      PartialCompletionState n r U D v t C →
      shortCount C = s →
      ∃ A : Fin n → Finset α,
        PartialCompletionState n r U D v t A ∧
        (∀ i : Fin n, (A i).card = r + 1) ∧
        Finset.univ.biUnion A = U
  have hMain : ∀ s : ℕ, P s := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro C hC hs
      by_cases hsZero : s = 0
      · have hShortEmpty :
            Finset.univ.filter (fun i : Fin n => (C i).card = r) = ∅ := by
          apply Finset.card_eq_zero.mp
          change shortCount C = 0
          exact hs.trans hsZero
        have hFull (i : Fin n) : (C i).card = r + 1 := by
          rcases hC.size i with hi | hi
          · have hiMem : i ∈ Finset.univ.filter
                (fun j : Fin n => (C j).card = r) := by simp [hi]
            simp [hShortEmpty] at hiMem
          · exact hi
        have hUnionSub : Finset.univ.biUnion C ⊆ U := by
          intro x hx
          obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
          exact (hC.1 i).1 hxi
        have hUnallocZero : (U \ Finset.univ.biUnion C).card = 0 := by
          rw [hC.unallocated_count hTotal]
          exact Finset.card_eq_zero.mpr hShortEmpty
        have hUnallocEmpty : U \ Finset.univ.biUnion C = ∅ :=
          Finset.card_eq_zero.mp hUnallocZero
        have hUSub : U ⊆ Finset.univ.biUnion C := by
          intro x hxU
          by_contra hxNot
          have hx : x ∈ U \ Finset.univ.biUnion C :=
            Finset.mem_sdiff.mpr ⟨hxU, hxNot⟩
          simp [hUnallocEmpty] at hx
        exact ⟨C, hC, hFull,
          Finset.Subset.antisymm hUnionSub hUSub⟩
      have hsPos : 0 < s := by omega
      have hUnallocPos : 0 < (U \ Finset.univ.biUnion C).card := by
        rw [hC.unallocated_count hTotal]
        change 0 < shortCount C
        rw [hs]
        exact hsPos
      -- Exhaust real unused items first. Only when this set is empty may
      -- either of the manuscript's dummy-filling phases be entered.
      have hPick : ∃ e, e ∈ U \ Finset.univ.biUnion C ∧
          (e ∈ D → (U \ D) \ Finset.univ.biUnion C = ∅) := by
        by_cases hReal : ((U \ D) \ Finset.univ.biUnion C).Nonempty
        · obtain ⟨e,he⟩ := hReal
          have heReal : e ∈ U \ D := (Finset.mem_sdiff.mp he).1
          refine ⟨e,Finset.mem_sdiff.mpr
            ⟨(Finset.mem_sdiff.mp heReal).1,(Finset.mem_sdiff.mp he).2⟩,?_⟩
          intro heD
          exact False.elim ((Finset.mem_sdiff.mp heReal).2 heD)
        · obtain ⟨e,he⟩ := Finset.card_pos.mp hUnallocPos
          exact ⟨e,he,fun _ => Finset.not_nonempty_iff_eq_empty.mp hReal⟩
      obtain ⟨e,he,hRealExhausted⟩ := hPick
      obtain ⟨i, hiShort⟩ := exists_short_of_unallocated n r U C
        (fun j => (hC.1 j).1) hC.2.1 hTotal
        (fun j => hC.size j) ⟨e, he⟩
      have hShort : (C i).card = r ∧ v (C i) = t :=
        ⟨hiShort, hC.short_value i hiShort⟩
      have heNot (j : Fin n) : e ∉ C j := by
        intro heCj
        exact (Finset.mem_sdiff.mp he).2
          (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, heCj⟩)
      by_cases heD : e ∈ D
      · have hNoRealUnused : (U \ D) \ Finset.univ.biUnion C = ∅ :=
          hRealExhausted heD
        by_cases hFreeShort :
            ∃ j : Fin n, (C j).card = r ∧ C j ∩ D = ∅
        · obtain ⟨j, hjShort, hjFree⟩ := hFreeShort
          have hCap : (insert e (C j) ∩ D).card ≤ 1 :=
            (short_bundle_fill_dummy_count (C j) D e heD hjFree).le
          let C' := Function.update C j (insert e (C j))
          have hC' : PartialCompletionState n r U D v t C' :=
            hC.fill_unused j ⟨hjShort, hC.short_value j hjShort⟩ e he hCap
          have hLt : shortCount C' < s := by
            have hStep := short_count_decreases_after_fill
              n r C j hjShort e (heNot j)
            change shortCount C' < shortCount C at hStep
            rw [hs] at hStep
            exact hStep
          exact ih (shortCount C') hLt C' hC' rfl
        · have hNoShortFree (j : Fin n)
              (hjFree : C j ∩ D = ∅) : (C j).card = r + 1 := by
            rcases hC.size j with hjShort | hjFull
            · exact False.elim (hFreeShort ⟨j, hjShort, hjFree⟩)
            · exact hjFull
          obtain ⟨C', hC', hLtRaw⟩ :=
            hC.swap_fill hD i hShort e heD he hNoShortFree
          have hLt : shortCount C' < s := by
            change shortCount C' < shortCount C at hLtRaw
            rw [hs] at hLtRaw
            exact hLtRaw
          exact ih (shortCount C') hLt C' hC' rfl
      · have hCap : (insert e (C i) ∩ D).card ≤ 1 := by
          rw [short_bundle_fill_real_dummy_count (C i) D e heD]
          exact hC.2.2 i
        let C' := Function.update C i (insert e (C i))
        have hC' : PartialCompletionState n r U D v t C' :=
          hC.fill_unused i hShort e he hCap
        have hLt : shortCount C' < s := by
          have hStep := short_count_decreases_after_fill
            n r C i hiShort e (heNot i)
          change shortCount C' < shortCount C at hStep
          rw [hs] at hStep
          exact hStep
        exact ih (shortCount C') hLt C' hC' rfl
  exact hMain (shortCount B) B hB rfl

end FairDivision.Finite
