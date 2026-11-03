import FairDivision.Topology.FiniteSimplexProduct
import FairDivision.Finite.BundlesToAllocation
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Independent products of compatible child lotteries

BF Section 4 combines the child lotteries on disjoint actual item stocks.
The probability of an outcome tuple is the literal product of the child
probabilities. Flattening the child and position indices changes only the
names of positions. Each combined bundle and every coordinate marginal are
exactly the corresponding child bundle and child marginal.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.Recording

open scoped BigOperators Classical
open FairDivision.Finite

/-- The manuscript's independent product, with all compatibility and
expectation guarantees on the common parent inventory. No positivity of
`a` or `p` is needed by this finite construction. -/
theorem exists_equitable_product_lottery {p a N r c : ℕ}
    {D : Finset (Fin N)}
    (μ : Fin p → stdSimplex ℝ (PartialVertex a D r c))
    (hCompatible : ∀ i, μ i ∈ compatibleLotterySpace a N r c D)
    (E : Fin p → Finset (Fin N))
    (hPool : ∀ i j, pool (lotterySupport (μ i)) j ⊆ E i)
    (hPair : ∀ i j : Fin p, i ≠ j → Disjoint (E i) (E j))
    (w : Finset (Fin N) → ℝ) (t : ℝ)
    (hMean : ∀ i j, (∑ X : PartialVertex a D r c,
      (μ i).1 X * w (partialBundle X.1 j)) = t) :
    ∃ ν : stdSimplex ℝ (PartialVertex (a*p) D r c),
      ν ∈ compatibleLotterySpace (a*p) N r c D ∧
      (∀ j, pool (lotterySupport ν) j ⊆ Finset.univ.biUnion E) ∧
      ∀ j, (∑ X : PartialVertex (a*p) D r c,
        ν.1 X * w (partialBundle X.1 j)) = t := by
  classical
  -- `finiteSimplexProduct` constructs the function-space Fintype using
  -- the classical equality on its abstract index type. Keep that SAME
  -- equality when specializing the product and its support to `Fin p`.
  letI : DecidableEq (Fin p) := Classical.decEq (Fin p)
  let σ : Fin (a*p) ≃ Fin p × Fin a :=
    (finProdFinEquiv : Fin a × Fin p ≃ Fin (a*p)).symm.trans
      (Equiv.prodComm _ _)
  let C : Fin (a*p) → Finset (Fin N) := fun j =>
    pool (lotterySupport (μ (σ j).1)) (σ j).2
  have hC : ∀ j, C j ⊆ E (σ j).1 := fun j => hPool _ _
  have hCPair : ∀ j k : Fin (a*p), j ≠ k → Disjoint (C j) (C k) := by
    intro j k hjk
    by_cases hi : (σ j).1 = (σ k).1
    · have hs : (σ j).2 ≠ (σ k).2 := by
        intro hs
        exact hjk (σ.injective (Prod.ext hi hs))
      have hc := (hCompatible (σ k).1).1 (σ j).2 (σ k).2 hs
      simpa only [C, hi] using hc
    · exact (hPair _ _ hi).mono (hC j) (hC k)
  let Good : (Fin p → PartialVertex a D r c) → Prop :=
    fun X => ∀ i, X i ∈ lotterySupport (μ i)
  let B : (Fin p → PartialVertex a D r c) → Fin (a*p) → Finset (Fin N) :=
    fun X j => partialBundle (X (σ j).1).1 (σ j).2
  have hB : ∀ X, Good X → ∀ j, B X j ⊆ C j := by
    intro X hX j
    exact partialBundle_subset_pool (hX _) _
  have hBPair : ∀ X, Good X → ∀ j k : Fin (a*p), j ≠ k →
      Disjoint (B X j) (B X k) := by
    intro X hX j k hjk
    exact (hCPair j k hjk).mono (hB X hX j) (hB X hX k)
  let combine : (X : Fin p → PartialVertex a D r c) → Good X →
      PartialVertex (a*p) D r c := fun X hX =>
    ⟨partialAllocationFromBundles (B X), by
      intro j
      rw [partialBundle_fromBundles (B X) (hBPair X hX)]
      exact (X (σ j).1).2 (σ j).2⟩
  have hCombine : ∀ X hX j, partialBundle (combine X hX).1 j = B X j := by
    intro X hX j
    exact partialBundle_fromBundles (B X) (hBPair X hX) j
  have hDefault : ∃ X : Fin p → PartialVertex a D r c, Good X := by
    choose X hX using fun i : Fin p => lotterySupport_nonempty (μ i)
    exact ⟨X, hX⟩
  obtain ⟨X₀, hX₀⟩ := hDefault
  -- Values off the positive support have probability zero. A fixed valid
  -- default makes the finite pushforward a total function on all tuples.
  let f : (Fin p → PartialVertex a D r c) → PartialVertex (a*p) D r c :=
    fun X => if hX : Good X then combine X hX else combine X₀ hX₀
  let P := finiteSimplexProduct μ
  have hSupport : ∀ X, X ∈ finiteSimplexSupport P → Good X := by
    intro X hX i
    exact finiteSimplexProduct_support μ hX i
  have hf : ∀ X, Good X → ∀ j, partialBundle (f X).1 j = B X j := by
    intro X hX j
    dsimp only [f]
    rw [dif_pos hX]
    exact hCombine X hX j
  let ν := stdSimplex.map f P
  have hTargetPool : ∀ j, pool (lotterySupport ν) j ⊆ C j := by
    intro j g hg
    obtain ⟨_, Y, hY, hYg⟩ := Finset.mem_filter.mp hg
    have hYs : Y ∈ finiteSimplexSupport ν := hY
    obtain ⟨X, hX, hXY⟩ := Finset.mem_image.mp
      (finiteSimplexSupport_map_subset f P hYs)
    have hb : g ∈ partialBundle (f X).1 j :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [hXY] using hYg⟩
    rw [hf X (hSupport X hX) j] at hb
    exact hB X (hSupport X hX) j hb
  refine ⟨ν, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro j k hjk
    exact (hCPair j k hjk).mono (hTargetPool j) (hTargetPool k)
  · intro j
    exact (Finset.card_le_card (Finset.inter_subset_inter (hTargetPool j) Finset.Subset.rfl)).trans
      ((hCompatible (σ j).1).2 (σ j).2)
  · intro j g hg
    exact Finset.mem_biUnion.mpr
      ⟨(σ j).1, Finset.mem_univ _, hC j (hTargetPool j hg)⟩
  · intro j
    change (∑ X, (stdSimplex.map f P).1 X * w (partialBundle X.1 j)) = t
    rw [finiteSimplexMap_expectation]
    calc
      (∑ X, P.1 X * w (partialBundle (f X).1 j)) =
          ∑ X, P.1 X * w (partialBundle (X (σ j).1).1 (σ j).2) := by
        apply Finset.sum_congr rfl
        intro X _
        by_cases hX : Good X
        · rw [hf X hX j]
        · have hz : P.1 X = 0 := by
            apply le_antisymm _ (P.2.1 X)
            apply le_of_not_gt
            intro hpos
            exact hX (hSupport X ((mem_finiteSimplexSupport_iff P X).mpr hpos))
          simp only [hz, zero_mul]
      _ = ∑ X : PartialVertex a D r c,
          (μ (σ j).1).1 X * w (partialBundle X.1 (σ j).2) :=
        finiteSimplexProduct_expectation μ (σ j).1
          (fun X => w (partialBundle X.1 (σ j).2))
      _ = t := hMean (σ j).1 (σ j).2

end FairDivision.Topology.Recording
