import FairDivision.BF.HeterogeneousShorteningState

/-!
# BF Section 5: real completion with donor certificates

The first completion phase must retain not only all value comparisons but
also the ability to shorten a dummy-free full bundle in the final balancing
step. This is the manuscript's same real-item insertion induction with that
additional invariant carried explicitly.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision.Finite

/-- Complete every real item while retaining the shortening certificate for
each dummy-free full donor bundle. -/
theorem complete_hetero_real_items_shortenable
    {n m r : ℕ} (U D : Finset (Fin m))
    (v : Fin n → Finset (Fin m) → ℝ) (τ : Fin n → ℝ)
    (hTotal : U.card = n * (r + 1))
    (B : Fin n → Finset (Fin m))
    (hB : HeteroPartialState r U D v τ B)
    (hShorten : HeteroShortenable r D v τ B) :
    ∃ C : Fin n → Finset (Fin m),
      HeteroPartialState r U D v τ C ∧
      HeteroShortenable r D v τ C ∧
      U \ D ⊆ Finset.univ.biUnion C := by
  classical
  let shortCount (C : Fin n → Finset (Fin m)) : ℕ :=
    (Finset.univ.filter (fun i : Fin n => (C i).card = r)).card
  let P : ℕ → Prop := fun s =>
    ∀ C : Fin n → Finset (Fin m),
      HeteroPartialState r U D v τ C →
      HeteroShortenable r D v τ C →
      shortCount C = s →
      ∃ A : Fin n → Finset (Fin m),
        HeteroPartialState r U D v τ A ∧
        HeteroShortenable r D v τ A ∧
        U \ D ⊆ Finset.univ.biUnion A
  have hMain : ∀ s : ℕ, P s := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro C hC hCShorten hs
      by_cases hUnused : ((U \ D) \ Finset.univ.biUnion C).Nonempty
      · obtain ⟨e, he⟩ := hUnused
        have heU : e ∈ U :=
          (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1
        have heNot : e ∉ Finset.univ.biUnion C :=
          (Finset.mem_sdiff.mp he).2
        have heRaw : e ∈ U \ Finset.univ.biUnion C :=
          Finset.mem_sdiff.mpr ⟨heU, heNot⟩
        obtain ⟨i, hi⟩ := exists_short_of_unallocated
          n r U C (fun j => (hC.1 j).1) hC.2.1 hTotal
          (fun j => hC.size j) ⟨e, heRaw⟩
        have heNotCi : e ∉ C i := by
          intro heCi
          exact heNot (Finset.mem_biUnion.mpr
            ⟨i, Finset.mem_univ _, heCi⟩)
        let C' := Function.update C i (insert e (C i))
        have hC' : HeteroPartialState r U D v τ C' :=
          hC.fill_real_unused i hi e he
        have hCShorten' : HeteroShortenable r D v τ C' :=
          HeteroShortenable.fill_real_unused hC hCShorten i hi e
        have hLt : shortCount C' < s := by
          have hStep := short_count_decreases_after_fill
            n r C i hi e heNotCi
          change shortCount C' < shortCount C at hStep
          rw [hs] at hStep
          exact hStep
        exact ih (shortCount C') hLt C' hC' hCShorten' rfl
      · have hCovered : U \ D ⊆ Finset.univ.biUnion C := by
          intro x hx
          by_contra hNot
          exact hUnused ⟨x, Finset.mem_sdiff.mpr ⟨hx, hNot⟩⟩
        exact ⟨C, hC, hCShorten, hCovered⟩
  exact hMain (shortCount B) B hB hShorten rfl

end FairDivision.BF
