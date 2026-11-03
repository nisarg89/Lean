import FairDivision.BF.VirtualDummyTransport
import FairDivision.BF.HeterogeneousNoDummyEndpoint
import FairDivision.BF.VirtualScoreBridge

/-!
# Removing an unused virtual placeholder

When there are no actual dummy items, a reduced marginal never uses its
placeholder coordinate. Relabeling only the occupied stock is then injective,
even though a map from all `N+1` virtual labels to `N` actual labels cannot be.
This transports the manuscript's owner witnesses to the exactly divisible
finite endpoint.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision.Topology
open FairDivision.Finite

/-- An owner witness can be relabeled by a function that is injective on its
available stock. Valuation agreement is needed only on subsets of that stock. -/
noncomputable def OwnerWitness.imageOnStock
    {n m N q : ℕ} {dummy : Fin m}
    {v₀ : Fin n → Finset (Fin m) → ℝ}
    {v : Fin n → Finset (Fin N) → ℝ}
    {E : Finset (Fin m)} {u : Fin n → ℝ} {owner : Fin n}
    (f : Fin m → Fin N) (hf : Set.InjOn f E)
    (hval : ∀ j : Fin n, ∀ S : Finset (Fin m), S ⊆ E →
      v j (S.image f) = v₀ j S)
    (h : OwnerWitness q dummy v₀ E u owner) :
    OwnerWitness q (f dummy) v (E.image f) u owner := by
  classical
  have hInj (S : Finset (Fin m)) (hSE : S ⊆ E) :
      Set.InjOn f S := hf.mono (Finset.coe_subset.mpr hSE)
  have hCard (S : Finset (Fin m)) (hSE : S ⊆ E) :
      (S.image f).card = S.card :=
    Finset.card_image_of_injOn (hInj S hSE)
  have hLowerE : h.lowerSet ⊆ E := h.lower_subset.trans h.in_stock
  have hUpperE : h.upperSet ⊆ E := h.upper_subset.trans h.in_stock
  refine {
    B := h.B.image f
    lowerSet := h.lowerSet.image f
    upperSet := h.upperSet.image f
    in_stock := Finset.image_subset_image h.in_stock
    size := ?_
    lower_subset := Finset.image_subset_image h.lower_subset
    upper_subset := Finset.image_subset_image h.upper_subset
    lower_size := ?_
    upper_size := ?_
    lower_bound := ?_
    owner_bound := ?_
    short_sets := ?_
    shortening := ?_
  }
  · rcases h.size with hShort | hFull
    · exact Or.inl (by simpa only [hCard h.B h.in_stock] using hShort)
    · exact Or.inr (by simpa only [hCard h.B h.in_stock] using hFull)
  · simpa only [hCard h.lowerSet hLowerE] using h.lower_size
  · simpa only [hCard h.upperSet hUpperE] using h.upper_size
  · intro j
    calc
      v j (h.lowerSet.image f) = v₀ j h.lowerSet := hval j h.lowerSet hLowerE
      _ ≤ u j := h.lower_bound j
  · calc
      u owner ≤ v₀ owner h.upperSet := h.owner_bound
      _ = v owner (h.upperSet.image f) := (hval owner h.upperSet hUpperE).symm
  · intro hShort
    have hShort' : h.B.card = q - 1 := by
      simpa only [hCard h.B h.in_stock] using hShort
    obtain ⟨hLower, hUpper⟩ := h.short_sets hShort'
    exact ⟨congrArg (fun S : Finset (Fin m) => S.image f) hLower,
      congrArg (fun S : Finset (Fin m) => S.image f) hUpper⟩
  · intro hFull hNoDummy
    have hFull' : h.B.card = q := by
      simpa only [hCard h.B h.in_stock] using hFull
    have hNoDummy' : dummy ∉ h.B := by
      intro hd
      exact hNoDummy (Finset.mem_image.mpr ⟨dummy, hd, rfl⟩)
    obtain ⟨C, hCB, hCsize, hLower, hUpper⟩ :=
      h.shortening hFull' hNoDummy'
    have hCE : C ⊆ E := hCB.trans h.in_stock
    have hCInj : Set.InjOn f C := hInj C hCE
    refine ⟨C.image f, Finset.image_subset_image hCB, ?_, ?_, ?_⟩
    · simpa only [hCard C hCE] using hCsize
    · intro j
      obtain ⟨Z, hZ, hValue⟩ := hLower j
      refine ⟨Z.image f, ?_, ?_⟩
      · exact ⟨Finset.image_subset_image hZ.1,
          (by simpa only [hCard Z (hZ.1.trans hCE)] using hZ.2)⟩
      · calc
          v j (C.image f \ Z.image f) = v j ((C \ Z).image f) := by
            rw [Finset.image_sdiff_of_injOn hCInj hZ.1]
          _ = v₀ j (C \ Z) :=
            hval j (C \ Z) (Finset.sdiff_subset.trans hCE)
          _ ≤ u j := hValue
    · obtain ⟨Z, hZ, hValue⟩ := hUpper
      refine ⟨Z.image f, ?_, ?_⟩
      · exact ⟨Finset.image_subset_image hZ.1,
          (by simpa only [hCard Z (hZ.1.trans hCE)] using hZ.2)⟩
      · calc
          u owner ≤ v₀ owner (C \ Z) := hValue
          _ = v owner ((C \ Z).image f) :=
            (hval owner (C \ Z) (Finset.sdiff_subset.trans hCE)).symm
          _ = v owner (C.image f \ Z.image f) := by
            rw [Finset.image_sdiff_of_injOn hCInj hZ.1]

/-- The placeholder relabeling remains injective when restricted to a stock
that does not contain the placeholder. -/
theorem actualMarginalItem_injOn_avoiding_zero {N : ℕ}
    (D : Finset (Fin N)) (dummy : Fin N)
    (S : Finset (Fin (N - D.card + 1)))
    (hZero : (0 : Fin (N - D.card + 1)) ∉ S) :
    Set.InjOn (actualMarginalItem D dummy) S := by
  intro a ha b hb hab
  cases a using Fin.cases with
  | zero => exact False.elim (hZero ha)
  | succ a =>
      cases b using Fin.cases with
      | zero => exact False.elim (hZero hb)
      | succ b =>
          simp only [actualMarginalItem_succ] at hab
          have h : realItemEquiv D a = realItemEquiv D b := Subtype.ext hab
          exact congrArg Fin.succ ((realItemEquiv D).injective h)

/-- If the virtual dummy is absent, translating a bundle to actual labels
preserves its real part regardless of the chosen fallback item. -/
theorem pullbackRealBundle_actualMarginalItem_image_avoiding_zero {N : ℕ}
    (D : Finset (Fin N)) (dummy : Fin N)
    (S : Finset (Fin (N - D.card + 1)))
    (hZero : (0 : Fin (N - D.card + 1)) ∉ S) :
    pullbackRealBundle D (S.image (actualMarginalItem D dummy)) =
      marginalRealPart S := by
  ext g
  simp only [pullbackRealBundle, marginalRealPart, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hg
    obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hg
    cases a using Fin.cases with
    | zero => exact False.elim (hZero ha)
    | succ a =>
        have h : (realItemEquiv D a).val =
            (realItemEquiv D g).val := by
          simpa only [actualMarginalItem_succ] using heq
        have hag : a = g := (realItemEquiv D).injective (Subtype.ext h)
        exact hag ▸ ha
  · intro hg
    exact Finset.mem_image.mpr
      ⟨g.succ, hg, actualMarginalItem_succ D dummy g⟩

/-- With no actual dummies, every supported reduced marginal bundle omits
its virtual placeholder. -/
theorem zero_not_mem_reducedMarginalStock_empty
    {n N r : ℕ}
    (x : unlabeledLotterySpace n N r 1 (∅ : Finset (Fin N)))
    (i : Fin n) :
    (0 : Fin (N - (∅ : Finset (Fin N)).card + 1)) ∉
      finMarginalStock (unlabeledReducedMarginal i x) := by
  intro hZero
  obtain ⟨p, _hp, hZeroP⟩ :=
    exists_source_of_reducedMarginalStock_mem x i 0 hZero
  obtain ⟨X, hX⟩ := p.2
  have hCount : (p.1 i).2 = 0 := by
    rw [← congrArg Prod.snd (congrFun hX i)]
    simp [dummyProfileOf]
  have hImpossible :
      (0 : Fin (N - (∅ : Finset (Fin N)).card + 1)) ∉
        (reducedMarginalVertex p i).1 := by
    classical
    intro h
    have hUnion :
        (0 : Fin (N - (∅ : Finset (Fin N)).card + 1)) ∈
          (pullbackRealBundle ∅ (p.1 i).1).image Fin.succ ∪ ∅ := by
      simpa [reducedMarginalVertex, reducedMarginalBundle, hCount] using h
    rcases Finset.mem_union.mp hUnion with hImage | hEmpty
    · obtain ⟨g, _, hEq⟩ := Finset.mem_image.mp hImage
      exact (Fin.succ_ne_zero g) hEq
    · cases hEmpty
  exact hImpossible hZeroP

/-- Convert a virtual owner witness to an actual-item witness in the
exactly divisible case, using only local stock injectivity. -/
noncomputable def OwnerWitness.actualNoDummy
    {n N q : ℕ}
    (dummy : Fin N)
    (v : Fin n → Finset (Fin (N - (∅ : Finset (Fin N)).card)) → ℝ)
    (E : Finset (Fin (N - (∅ : Finset (Fin N)).card + 1)))
    (hZero : (0 : Fin (N - (∅ : Finset (Fin N)).card + 1)) ∉ E)
    (u : Fin n → ℝ) (owner : Fin n)
    (h : OwnerWitness q 0
      (fun j S => v j (marginalRealPart S)) E u owner) :
    OwnerWitness q dummy
      (fun j S => v j (pullbackRealBundle ∅ S))
      (E.image (actualMarginalItem ∅ dummy)) u owner := by
  have hval : ∀ j : Fin n,
      ∀ S : Finset (Fin (N - (∅ : Finset (Fin N)).card + 1)),
      S ⊆ E →
      (fun j S => v j (pullbackRealBundle ∅ S)) j
          (S.image (actualMarginalItem ∅ dummy)) =
        (fun j S => v j (marginalRealPart S)) j S := by
    intro j S hSE
    exact congrArg (v j)
      (pullbackRealBundle_actualMarginalItem_image_avoiding_zero
        ∅ dummy S (fun h0 => hZero (hSE h0)))
  simpa only [actualMarginalItem_zero] using
    (OwnerWitness.imageOnStock
      (actualMarginalItem ∅ dummy)
      (actualMarginalItem_injOn_avoiding_zero ∅ dummy E hZero)
      hval h)

/-- In the absence of actual dummies, a compatible labeled face provides
pairwise disjoint pools containing every translated marginal-stock item. -/
theorem exists_compatible_pools_for_reducedMarginals_empty
    {n N r : ℕ}
    (x : unlabeledLotterySpace n N r 1 (∅ : Finset (Fin N)))
    (dummy : Fin N) :
    ∃ T : Finset (PartialVertex n (∅ : Finset (Fin N)) r 1),
      IsCompatibleFamily T ∧
      T.image toUnlabeledDummyVertex =
        unlabeledLotterySupport x.1 ∧
      ∀ i : Fin n,
        (finMarginalStock (unlabeledReducedMarginal i x)).image
          (actualMarginalItem ∅ dummy) ⊆ pool T i := by
  classical
  obtain ⟨T, hT, hImage⟩ := x.2
  refine ⟨T, hT, hImage, ?_⟩
  intro i
  apply actualMarginalItem_image_subset ∅ dummy
    (finMarginalStock (unlabeledReducedMarginal i x)) (pool T i)
  · intro hZero
    exact False.elim ((zero_not_mem_reducedMarginalStock_empty x i) hZero)
  · intro g hSucc
    obtain ⟨p, hp, hSuccP⟩ :=
      exists_source_of_reducedMarginalStock_mem x i g.succ hSucc
    have hgReal : g ∈ pullbackRealBundle ∅ (p.1 i).1 := by
      rw [← marginalRealPart_reducedVertex p i]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ g, hSuccP⟩
    have hpImage : p ∈ T.image toUnlabeledDummyVertex := by
      rw [hImage]
      exact hp
    obtain ⟨X, hXT, hXp⟩ := Finset.mem_image.mp hpImage
    rw [← hXp] at hgReal
    change g ∈ pullbackRealBundle ∅ (partialBundle X.1 i \ ∅) at hgReal
    have hActual : (realItemEquiv ∅ g).val ∈ partialBundle X.1 i := by
      have hgSDiff : (realItemEquiv ∅ g).val ∈
          partialBundle X.1 i \ (∅ : Finset (Fin N)) := by
        exact (Finset.mem_filter.mp hgReal).2
      exact (Finset.mem_sdiff.mp hgSDiff).1
    exact partialBundle_subset_pool hXT i hActual

/-- The finite BF allocation conversion also follows from a virtual-envy-
free point when the augmented instance has no dummy items. -/
theorem exists_balanced_ef11_of_virtualEnvyFree_emptyDummy
    {n N q : ℕ} (hn : 0 < n)
    (v : Fin n → Finset (Fin (N - (∅ : Finset (Fin N)).card)) → ℝ)
    (spec : VirtualValuationSpec (q := q) v)
    (x : unlabeledLotterySpace n N (q - 1) 1 (∅ : Finset (Fin N)))
    (hVirtualEF : ∀ i j : Fin n,
      spec.score (unlabeledReducedMarginal j x) i ≤
        spec.score (unlabeledReducedMarginal i x) i)
    (hq : 2 ≤ q) (hN : N = n * q) :
    ∃ A : FairDivision.Allocation n (N - (∅ : Finset (Fin N)).card),
      FairDivision.IsBalanced A ∧ FairDivision.IsEF11 v A := by
  classical
  have hNpos : 0 < N := by
    rw [hN]
    exact Nat.mul_pos hn (by omega)
  let dummy : Fin N := ⟨0, hNpos⟩
  obtain ⟨T, hT, _hImage, hStock⟩ :=
    exists_compatible_pools_for_reducedMarginals_empty x dummy
  let E : Fin n → Finset (Fin N) := fun i => pool T i
  let u : Fin n → Fin n → ℝ :=
    fun s i => spec.score (unlabeledReducedMarginal s x) i
  have hWitness (s : Fin n) :
      Nonempty (OwnerWitness q dummy
        (fun j S => v j (pullbackRealBundle ∅ S))
        (E s) (u s) s) := by
    obtain ⟨h⟩ := spec.admissible_score (unlabeledReducedMarginal s x) s
    exact ⟨(OwnerWitness.actualNoDummy dummy v
      (finMarginalStock (unlabeledReducedMarginal s x))
      (zero_not_mem_reducedMarginalStock_empty x s)
      (spec.score (unlabeledReducedMarginal s x)) s h).enlarge (hStock s)⟩
  let w (s : Fin n) : OwnerWitness q dummy
      (fun j S => v j (pullbackRealBundle ∅ S))
      (E s) (u s) s := Classical.choice (hWitness s)
  have hEF : ∀ i j : Fin n, u j i ≤ u i i := by
    intro i j
    exact hVirtualEF i j
  have hPools : ∀ i j : Fin n, i ≠ j → Disjoint (E i) (E j) :=
    hT.1
  exact hetero_selectedWitness_no_dummy_exists_balanced_ef11
    dummy v E u w hq hN hn hEF hPools

/-- Equalized virtual position scores at every positive tolerance imply the
BF allocation in the exactly divisible case, conditional on virtual values. -/
theorem exists_balanced_ef11_of_equalized_virtualScores_emptyDummy
    {n N q : ℕ} (hn : 0 < n)
    (v : Fin n → Finset (Fin (N - (∅ : Finset (Fin N)).card)) → ℝ)
    (spec : VirtualValuationSpec (q := q) v)
    (hEqual : ∀ ε : ℝ, 0 < ε →
      ∃ x : unlabeledLotterySpace n N (q - 1) 1
        (∅ : Finset (Fin N)),
        ∀ s t : Fin n,
          positionScore hn (fun i z => spec.score z i) ε
            (fun a => unlabeledReducedMarginal a x) s =
          positionScore hn (fun i z => spec.score z i) ε
            (fun a => unlabeledReducedMarginal a x) t)
    (hq : 2 ≤ q) (hN : N = n * q) :
    ∃ A : FairDivision.Allocation n (N - (∅ : Finset (Fin N)).card),
      FairDivision.IsBalanced A ∧ FairDivision.IsEF11 v A := by
  obtain ⟨x, hVirtualEF⟩ :=
    exists_virtualEnvyFree_of_equalized_scores hn ∅ v spec hEqual
  exact exists_balanced_ef11_of_virtualEnvyFree_emptyDummy
    hn v spec x hVirtualEF hq hN

end FairDivision.BF
