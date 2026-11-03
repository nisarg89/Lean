import FairDivision.BF.HeterogeneousBrackets
import FairDivision.Finite.ShortBundleFill
import FairDivision.Finite.PartialCompletionFill

/-!
# BF Section 5: completing all real items

The selected virtual-valuation bundles are short or full. Each unused real
item can be appended to a short bundle while preserving every agent's
comparison: deleting the appended item recovers the certified short bundle.
Strong induction on the number of short bundles continues until all real
items have been assigned. Dummies may remain unused at this stage, as in the
manuscript's heterogeneous conversion.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision.Finite

/-- The heterogeneous bundle alternative maintained while appending real
items. A short bundle itself supplies all comparisons; a full bundle has
observer and owner optional-deletion brackets. -/
def HeteroShortOrFull {n m : ℕ}
    (v : Fin n → Finset (Fin m) → ℝ) (τ : Fin n → ℝ)
    (r : ℕ) (owner : Fin n) (B : Finset (Fin m)) : Prop :=
  (B.card = r ∧ (∀ j : Fin n, v j B ≤ τ j) ∧ τ owner ≤ v owner B) ∨
    (B.card = r + 1 ∧ HeteroBrackets v τ owner B)

/-- The simultaneous partial-bundle invariant used in the first completion
phase of BF Section 5. -/
def HeteroPartialState {n m : ℕ}
    (r : ℕ) (U D : Finset (Fin m))
    (v : Fin n → Finset (Fin m) → ℝ) (τ : Fin n → ℝ)
    (B : Fin n → Finset (Fin m)) : Prop :=
  (∀ i, B i ⊆ U ∧ HeteroShortOrFull v τ r i (B i)) ∧
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i, (B i ∩ D).card ≤ 1)

theorem HeteroPartialState.size
    {n m r : ℕ} {U D : Finset (Fin m)}
    {v : Fin n → Finset (Fin m) → ℝ} {τ : Fin n → ℝ}
    {B : Fin n → Finset (Fin m)}
    (h : HeteroPartialState r U D v τ B) (i : Fin n) :
    (B i).card = r ∨ (B i).card = r + 1 := by
  exact ((h.1 i).2).elim (fun hs => Or.inl hs.1) (fun hf => Or.inr hf.1)

theorem HeteroPartialState.short_values
    {n m r : ℕ} {U D : Finset (Fin m)}
    {v : Fin n → Finset (Fin m) → ℝ} {τ : Fin n → ℝ}
    {B : Fin n → Finset (Fin m)}
    (h : HeteroPartialState r U D v τ B)
    (i : Fin n) (hi : (B i).card = r) :
    (∀ j : Fin n, v j (B i) ≤ τ j) ∧ τ i ≤ v i (B i) := by
  rcases (h.1 i).2 with hs | hf
  · exact ⟨hs.2.1, hs.2.2⟩
  · omega

theorem HeteroPartialState.full_brackets
    {n m r : ℕ} {U D : Finset (Fin m)}
    {v : Fin n → Finset (Fin m) → ℝ} {τ : Fin n → ℝ}
    {B : Fin n → Finset (Fin m)}
    (h : HeteroPartialState r U D v τ B)
    (i : Fin n) (hi : (B i).card = r + 1) :
    HeteroBrackets v τ i (B i) := by
  rcases (h.1 i).2 with hs | hf
  · omega
  · exact hf.2

/-- The selected virtual-valuation bundles form the initial heterogeneous
completion state. -/
theorem heteroState_of_selectedWitness
    {n m q : ℕ} {dummy : Fin m}
    {v : Fin n → Finset (Fin m) → ℝ}
    {E : Fin n → Finset (Fin m)}
    {u : Fin n → Fin n → ℝ}
    (w : ∀ s : Fin n, OwnerWitness q dummy v (E s) (u s) s)
    (hEF : ∀ i j : Fin n, u j i ≤ u i i)
    (hPools : ∀ i j : Fin n, i ≠ j → Disjoint (E i) (E j))
    (U D : Finset (Fin m))
    (hEU : ∀ i, E i ⊆ U)
    (hCap : ∀ i, (E i ∩ D).card ≤ 1)
    (hq : 1 ≤ q) :
    HeteroPartialState (q - 1) U D v (fun j => u j j)
      (fun i => (w i).B) := by
  classical
  refine ⟨?_, selectedWitness_disjoint w hPools, ?_⟩
  · intro i
    constructor
    · exact (w i).in_stock.trans (hEU i)
    · rcases (w i).size with hShort | hFull
      · obtain ⟨hLower, hUpper⟩ :=
          selectedWitness_short_values w hEF i hShort
        exact Or.inl ⟨hShort, hLower, hUpper⟩
      · have hCard : (w i).B.card = q - 1 + 1 := by
          simpa only [Nat.sub_add_cancel hq] using hFull
        exact Or.inr ⟨hCard, selectedWitness_brackets w hEF i⟩
  · intro i
    have hSub : (w i).B ∩ D ⊆ E i ∩ D := by
      intro x hx
      exact Finset.mem_inter.mpr
        ⟨(w i).in_stock (Finset.mem_inter.mp hx).1,
          (Finset.mem_inter.mp hx).2⟩
    exact (Finset.card_le_card hSub).trans (hCap i)

/-- One unused real item fills one short position and preserves the
heterogeneous completion invariant. -/
theorem HeteroPartialState.fill_real_unused
    {n m r : ℕ} {U D : Finset (Fin m)}
    {v : Fin n → Finset (Fin m) → ℝ} {τ : Fin n → ℝ}
    {B : Fin n → Finset (Fin m)}
    (h : HeteroPartialState r U D v τ B)
    (i : Fin n) (hi : (B i).card = r)
    (e : Fin m)
    (he : e ∈ (U \ D) \ Finset.univ.biUnion B) :
    HeteroPartialState r U D v τ
      (Function.update B i (insert e (B i))) := by
  classical
  have heReal : e ∈ U \ D := (Finset.mem_sdiff.mp he).1
  have heU : e ∈ U := (Finset.mem_sdiff.mp heReal).1
  have heD : e ∉ D := (Finset.mem_sdiff.mp heReal).2
  have heUnused (j : Fin n) : e ∉ B j := by
    intro heBj
    exact (Finset.mem_sdiff.mp he).2
      (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, heBj⟩)
  have hOld := h.short_values i hi
  have hFillCard : (insert e (B i)).card = r + 1 := by
    simp [heUnused i, hi]
  have hFillBracket : HeteroBrackets v τ i (insert e (B i)) :=
    HeteroBrackets.insert_of_short hOld.1 hOld.2 e (heUnused i)
  refine ⟨?_, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      exact ⟨Finset.insert_subset heU (h.1 i).1,
        Or.inr ⟨hFillCard, hFillBracket⟩⟩
    · simpa [Function.update, hji] using h.1 j
  · intro j l hjl
    by_cases hji : j = i
    · subst j
      have hli : l ≠ i := Ne.symm hjl
      simp [Function.update, hli]
      exact ⟨heUnused l, h.2.1 i l hjl⟩
    · by_cases hli : l = i
      · subst l
        simp [Function.update, hji]
        exact ⟨heUnused j, h.2.1 j i hjl⟩
      · simpa [Function.update, hji, hli] using h.2.1 j l hjl
  · intro j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      rw [short_bundle_fill_real_dummy_count (B i) D e heD]
      exact h.2.2 i
    · simpa [Function.update, hji] using h.2.2 j

/-- Fill every unused real item, leaving at most unused dummies. The
construction follows the manuscript's first completion phase. -/
theorem complete_hetero_real_items
    {n m r : ℕ} (U D : Finset (Fin m))
    (v : Fin n → Finset (Fin m) → ℝ) (τ : Fin n → ℝ)
    (hTotal : U.card = n * (r + 1))
    (B : Fin n → Finset (Fin m))
    (hB : HeteroPartialState r U D v τ B) :
    ∃ C : Fin n → Finset (Fin m),
      HeteroPartialState r U D v τ C ∧
      U \ D ⊆ Finset.univ.biUnion C := by
  classical
  let shortCount (C : Fin n → Finset (Fin m)) : ℕ :=
    (Finset.univ.filter (fun i : Fin n => (C i).card = r)).card
  let P : ℕ → Prop := fun s =>
    ∀ C : Fin n → Finset (Fin m),
      HeteroPartialState r U D v τ C → shortCount C = s →
      ∃ A : Fin n → Finset (Fin m),
        HeteroPartialState r U D v τ A ∧
        U \ D ⊆ Finset.univ.biUnion A
  have hMain : ∀ s : ℕ, P s := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro C hC hs
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
        have hLt : shortCount C' < s := by
          have hStep := short_count_decreases_after_fill
            n r C i hi e heNotCi
          change shortCount C' < shortCount C at hStep
          rw [hs] at hStep
          exact hStep
        exact ih (shortCount C') hLt C' hC' rfl
      · have hCovered : U \ D ⊆ Finset.univ.biUnion C := by
          intro x hx
          by_contra hNot
          exact hUnused ⟨x, Finset.mem_sdiff.mpr ⟨hx, hNot⟩⟩
        exact ⟨C, hC, hCovered⟩
  exact hMain (shortCount B) B hB rfl

end FairDivision.BF
