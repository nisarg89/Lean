import FairDivision.BF.HeterogeneousShorteningState
import FairDivision.BF.HeterogeneousDummyProjection

/-!
# BF Section 5: state after removing dummy items

The manuscript's real bundles have three possible sizes. Deficient bundles
have direct value bounds, middle bundles have deletion brackets, and full
real bundles retain a certified shortening for the final rebalancing.
-/

set_option autoImplicit false

namespace FairDivision.BF

/-- Per-bundle certificates needed after the manuscript removes dummies. -/
def HeteroRealBundle {n m : ℕ}
    (r : ℕ) (v : Fin n → Finset (Fin m) → ℝ) (τ : Fin n → ℝ)
    (owner : Fin n) (R : Finset (Fin m)) : Prop :=
  (R.card = r - 1 ∧
    (∀ j : Fin n, v j R ≤ τ j) ∧ τ owner ≤ v owner R) ∨
  (R.card = r ∧ HeteroBrackets v τ owner R) ∨
  (R.card = r + 1 ∧ HeteroBrackets v τ owner R ∧
    ∃ C : Finset (Fin m),
      C ⊆ R ∧ C.card = r ∧ HeteroBrackets v τ owner C)


/-- A deficient real bundle retains direct lower and upper comparisons. -/
theorem HeteroRealBundle.small_values
    {n m r : ℕ} {v : Fin n → Finset (Fin m) → ℝ}
    {τ : Fin n → ℝ} {owner : Fin n} {R : Finset (Fin m)}
    (h : HeteroRealBundle r v τ owner R)
    (hr : 1 ≤ r)
    (hSmall : R.card = r - 1) :
    (∀ j : Fin n, v j R ≤ τ j) ∧ τ owner ≤ v owner R := by
  rcases h with hs | hm | hf
  · exact ⟨hs.2.1, hs.2.2⟩
  · have hMiddle := hm.1
    omega
  · have hFull := hf.1
    omega

/-- A full real bundle has a certified shortening preserving every
heterogeneous comparison. -/
theorem HeteroRealBundle.full_shorten
    {n m r : ℕ} {v : Fin n → Finset (Fin m) → ℝ}
    {τ : Fin n → ℝ} {owner : Fin n} {R : Finset (Fin m)}
    (h : HeteroRealBundle r v τ owner R)
    (hFull : R.card = r + 1) :
    ∃ C : Finset (Fin m),
      C ⊆ R ∧ C.card = r ∧ HeteroBrackets v τ owner C := by
  rcases h with hs | hm | hf
  · have hSmall := hs.1
    omega
  · have hMiddle := hm.1
    omega
  · exact hf.2.2

/-- The augmented completion state and its shortening certificates provide
the three real-bundle alternatives after deleting dummies. -/
theorem HeteroPartialState.realBundle
    {n m r : ℕ} {U D : Finset (Fin m)}
    {v : Fin n → Finset (Fin m) → ℝ} {τ : Fin n → ℝ}
    {B : Fin n → Finset (Fin m)}
    (hState : HeteroPartialState r U D v τ B)
    (hShorten : HeteroShortenable r D v τ B)
    (hIgnore : ∀ j : Fin n, ∀ S : Finset (Fin m),
      v j (S \ D) = v j S)
    (i : Fin n) :
    HeteroRealBundle r v τ i (B i \ D) := by
  have hCap := hState.2.2 i
  have hCard := Finset.card_sdiff_add_card_inter (B i) D
  rcases (hState.1 i).2 with hShort | hFull
  · obtain ⟨hAugCard, hLower, hUpper⟩ := hShort
    obtain ⟨hRealLower, hRealUpper⟩ :=
      shortValues_realTrace hLower hUpper hIgnore
    by_cases hSmall : (B i \ D).card = r - 1
    · exact Or.inl ⟨hSmall, hRealLower, hRealUpper⟩
    · have hMiddle : (B i \ D).card = r := by omega
      exact Or.inr (Or.inl ⟨hMiddle,
        HeteroBrackets.of_short_values hRealLower hRealUpper⟩)
  · obtain ⟨hAugCard, hAugBrackets⟩ := hFull
    have hRealBrackets := hAugBrackets.realTrace hIgnore
    by_cases hMiddle : (B i \ D).card = r
    · exact Or.inr (Or.inl ⟨hMiddle, hRealBrackets⟩)
    · have hRealFull : (B i \ D).card = r + 1 := by omega
      have hNoDummyCard : (B i ∩ D).card = 0 := by omega
      have hNoDummy : B i ∩ D = ∅ := Finset.card_eq_zero.mp hNoDummyCard
      obtain ⟨C, hCB, hCcard, hCbrackets⟩ :=
        hShorten i hAugCard hNoDummy
      have hCReal : C ⊆ B i \ D := by
        intro x hxC
        have hxB : x ∈ B i := hCB hxC
        have hxNotD : x ∉ D := by
          intro hxD
          have hxInter : x ∈ B i ∩ D := Finset.mem_inter.mpr ⟨hxB, hxD⟩
          simpa [hNoDummy] using hxInter
        exact Finset.mem_sdiff.mpr ⟨hxB, hxNotD⟩
      exact Or.inr (Or.inr
        ⟨hRealFull, hRealBrackets, C, hCReal, hCcard,
          hCbrackets⟩)


/-- The post-projection finite state, including disjointness and coverage of
all real items. -/
def HeteroRealState {n m : ℕ}
    (r : ℕ) (Rstock : Finset (Fin m))
    (v : Fin n → Finset (Fin m) → ℝ) (τ : Fin n → ℝ)
    (R : Fin n → Finset (Fin m)) : Prop :=
  (∀ i, R i ⊆ Rstock ∧ HeteroRealBundle r v τ i (R i)) ∧
  (∀ i j, i ≠ j → Disjoint (R i) (R j)) ∧
  Rstock ⊆ Finset.univ.biUnion R

/-- Once the augmented completion covers every real item, removing all
dummies yields the finite state for the manuscript's rebalancing phase. -/
theorem HeteroPartialState.toRealState
    {n m r : ℕ} {U D : Finset (Fin m)}
    {v : Fin n → Finset (Fin m) → ℝ} {τ : Fin n → ℝ}
    {B : Fin n → Finset (Fin m)}
    (hState : HeteroPartialState r U D v τ B)
    (hShorten : HeteroShortenable r D v τ B)
    (hIgnore : ∀ j : Fin n, ∀ S : Finset (Fin m),
      v j (S \ D) = v j S)
    (hCovered : U \ D ⊆ Finset.univ.biUnion B) :
    HeteroRealState r (U \ D) v τ (fun i => B i \ D) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i
    constructor
    · exact Finset.sdiff_subset_sdiff (hState.1 i).1 (Finset.Subset.rfl)
    · exact hState.realBundle hShorten hIgnore i
  · intro i j hij
    exact (hState.2.1 i j hij).mono Finset.sdiff_subset Finset.sdiff_subset
  · intro x hx
    obtain ⟨i, _, hBi⟩ := Finset.mem_biUnion.mp (hCovered hx)
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _,
        Finset.mem_sdiff.mpr ⟨hBi, (Finset.mem_sdiff.mp hx).2⟩⟩

end FairDivision.BF
