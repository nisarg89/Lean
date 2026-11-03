import FairDivision.Definitions
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

/-!
# Compatible partial-allocation lotteries

The BF manuscript uses probability distributions over partial allocations with
pairwise disjoint position pools. This file records the finite combinatorial
interface. The topological realization and its connectivity come later.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- An item is either unassigned or assigned to one labeled position. -/
abbrev PartialAllocation (k m : ℕ) := Fin m → Option (Fin k)

/-- The items at position `i` in a partial allocation. -/
def partialBundle {k m : ℕ} (X : PartialAllocation k m)
    (i : Fin k) : Finset (Fin m) :=
  Finset.univ.filter (fun g => X g = some i)

/-- A partial allocation with every bundle of size `r` and at most `c`
items from the designated dummy set in each bundle. -/
def IsValidPartial {k m : ℕ} (D : Finset (Fin m)) (r c : ℕ)
    (X : PartialAllocation k m) : Prop :=
  ∀ i : Fin k, (partialBundle X i).card = r ∧
    ((partialBundle X i) ∩ D).card ≤ c

/-- Vertices of the compatibility complex for fixed parameters. -/
abbrev PartialVertex (k : ℕ) {m : ℕ} (D : Finset (Fin m)) (r c : ℕ) :=
  {X : PartialAllocation k m // IsValidPartial D r c X}

/-- The union of all bundles at position `i` over a family of vertices. -/
def pool {k m r c : ℕ} {D : Finset (Fin m)}
    (S : Finset (PartialVertex k D r c)) (i : Fin k) : Finset (Fin m) :=
  Finset.univ.filter (fun g => ∃ X ∈ S, X.1 g = some i)

/-- All positions have disjoint pools, and each pool contains at most `c`
dummies. Each vertex already has bundle size `r`. -/
def IsCompatibleFamily {k m r c : ℕ} {D : Finset (Fin m)}
    (S : Finset (PartialVertex k D r c)) : Prop :=
  (∀ i j : Fin k, i ≠ j → Disjoint (pool S i) (pool S j)) ∧
  (∀ i : Fin k, ((pool S i) ∩ D).card ≤ c)

/-- Passing to a subfamily only shrinks each pool. -/
theorem pool_mono {k m r c : ℕ} {D : Finset (Fin m)}
    {S T : Finset (PartialVertex k D r c)} (hST : S ⊆ T) (i : Fin k) :
    pool S i ⊆ pool T i := by
  classical
  intro g hg
  obtain ⟨_, X, hXS, hXg⟩ := Finset.mem_filter.mp hg
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, X, hST hXS, hXg⟩

/-- Every bundle in a supported partial allocation lies in its position pool. -/
theorem partialBundle_subset_pool {k m r c : ℕ} {D : Finset (Fin m)}
    {S : Finset (PartialVertex k D r c)} {X : PartialVertex k D r c}
    (hXS : X ∈ S) (i : Fin k) : partialBundle X.1 i ⊆ pool S i := by
  classical
  intro g hg
  have hXg : X.1 g = some i := (Finset.mem_filter.mp hg).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, X, hXS, hXg⟩

/-- Any choices inside distinct compatible pools are disjoint. -/
theorem choices_disjoint_of_compatible {k m r c : ℕ}
    {D : Finset (Fin m)} {S : Finset (PartialVertex k D r c)}
    (hS : IsCompatibleFamily S) (B : Fin k → Finset (Fin m))
    (hB : ∀ i, B i ⊆ pool S i) {i j : Fin k} (hij : i ≠ j) :
    Disjoint (B i) (B j) :=
  (hS.1 i j hij).mono (hB i) (hB j)

/-- Any choice inside a compatible pool inherits its dummy bound. -/
theorem choice_dummy_bound_of_compatible {k m r c : ℕ}
    {D : Finset (Fin m)} {S : Finset (PartialVertex k D r c)}
    (hS : IsCompatibleFamily S) (B : Fin k → Finset (Fin m))
    (hB : ∀ i, B i ⊆ pool S i) (i : Fin k) :
    ((B i) ∩ D).card ≤ c := by
  have hsubset : (B i) ∩ D ⊆ (pool S i) ∩ D := by
    intro g hg
    exact Finset.mem_inter.mpr ⟨hB i (Finset.mem_inter.mp hg).1,
      (Finset.mem_inter.mp hg).2⟩
  exact (Finset.card_le_card hsubset).trans (hS.2 i)

/-- Compatibility is hereditary under restriction of the lottery support. -/
theorem compatible_mono {k m r c : ℕ} {D : Finset (Fin m)}
    {S T : Finset (PartialVertex k D r c)}
    (hST : S ⊆ T) (hT : IsCompatibleFamily T) :
    IsCompatibleFamily S := by
  classical
  constructor
  · intro i j hij
    exact (hT.1 i j hij).mono (pool_mono hST i) (pool_mono hST j)
  · intro i
    have hsubset : pool S i ∩ D ⊆ pool T i ∩ D := by
      intro g hg
      exact Finset.mem_inter.mpr ⟨pool_mono hST i (Finset.mem_inter.mp hg).1,
        (Finset.mem_inter.mp hg).2⟩
    exact (Finset.card_le_card hsubset).trans (hT.2 i)

/-- For a one-vertex family, its position pool is the vertex bundle. -/
theorem pool_singleton {k m r c : ℕ} {D : Finset (Fin m)}
    (X : PartialVertex k D r c) (i : Fin k) :
    pool ({X} : Finset (PartialVertex k D r c)) i = partialBundle X.1 i := by
  classical
  ext g
  simp [pool, partialBundle]

/-- Each valid partial allocation is a compatible one-vertex lottery. -/
theorem compatible_singleton {k m r c : ℕ} {D : Finset (Fin m)}
    (X : PartialVertex k D r c) :
    IsCompatibleFamily ({X} : Finset (PartialVertex k D r c)) := by
  classical
  constructor
  · intro i j hij
    rw [pool_singleton, pool_singleton]
    apply Finset.disjoint_left.mpr
    intro g hgi hgj
    have hxi : X.1 g = some i := (Finset.mem_filter.mp hgi).2
    have hxj : X.1 g = some j := (Finset.mem_filter.mp hgj).2
    exact hij (Option.some.inj (hxi.symm.trans hxj))
  · intro i
    rw [pool_singleton]
    exact (X.2 i).2

/-- Compatible finite supports form an abstract simplicial complex. -/
def compatibilityComplex (k m r c : ℕ) (D : Finset (Fin m)) :
    AbstractSimplicialComplex (PartialVertex k D r c) where
  faces := {S | S.Nonempty ∧ IsCompatibleFamily S}
  isRelLowerSet_faces := by
    intro S hS
    exact ⟨hS.1, fun _ hsub hne => ⟨hne, compatible_mono hsub hS.2⟩⟩
  singleton_mem := by
    intro X
    exact ⟨Finset.singleton_nonempty X, compatible_singleton X⟩

noncomputable instance partialVertexFintype (k m r c : ℕ)
    (D : Finset (Fin m)) : Fintype (PartialVertex k D r c) := by
  classical
  infer_instance

/-- The strictly positive support of a probability vector on valid partial
allocations. -/
noncomputable def lotterySupport {k m r c : ℕ} {D : Finset (Fin m)}
    (lot : stdSimplex ℝ (PartialVertex k D r c)) :
    Finset (PartialVertex k D r c) := by
  classical
  exact Finset.univ.filter (fun X => 0 < lot.1 X)

/-- The geometric realization of the compatibility complex as a subspace of
the probability simplex on all valid partial allocations. -/
def compatibleLotterySpace (k m r c : ℕ) (D : Finset (Fin m)) :
    Set (stdSimplex ℝ (PartialVertex k D r c)) :=
  {lot | IsCompatibleFamily (lotterySupport lot)}

/-- A probability vector has at least one strictly positive coordinate. -/
theorem lotterySupport_nonempty {k m r c : ℕ} {D : Finset (Fin m)}
    (lot : stdSimplex ℝ (PartialVertex k D r c)) :
    (lotterySupport lot).Nonempty := by
  classical
  by_contra hnonempty
  have hzero : ∀ X : PartialVertex k D r c, lot.1 X = 0 := by
    intro X
    have hnot : ¬ 0 < lot.1 X := by
      intro hpos
      apply hnonempty
      exact ⟨X, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩⟩
    exact le_antisymm (le_of_not_gt hnot) (lot.2.1 X)
  have hsum := lot.2.2
  simp [hzero] at hsum

/-- The geometric-space condition agrees with membership of the support
in the compatibility complex. -/
theorem compatibleLottery_iff_support_face {k m r c : ℕ}
    {D : Finset (Fin m)}
    (lot : stdSimplex ℝ (PartialVertex k D r c)) :
    lot ∈ compatibleLotterySpace k m r c D ↔
      lotterySupport lot ∈ compatibilityComplex k m r c D := by
  change IsCompatibleFamily (lotterySupport lot) ↔
    (lotterySupport lot).Nonempty ∧ IsCompatibleFamily (lotterySupport lot)
  exact ⟨fun h => ⟨lotterySupport_nonempty lot, h⟩, fun h => h.2⟩

/-- A single valid partial allocation gives a point of the compatible
lottery space, concentrated entirely on that vertex. -/
theorem vertex_lottery_mem {k m r c : ℕ} {D : Finset (Fin m)}
    (X : PartialVertex k D r c) :
    (⟨Pi.single X (1 : ℝ), single_mem_stdSimplex ℝ X⟩ :
      stdSimplex ℝ (PartialVertex k D r c)) ∈
      compatibleLotterySpace k m r c D := by
  classical
  have hsupp : lotterySupport
      (⟨Pi.single X (1 : ℝ), single_mem_stdSimplex ℝ X⟩ :
        stdSimplex ℝ (PartialVertex k D r c)) = {X} := by
    ext Y
    simp only [lotterySupport, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, Pi.single_apply]
    by_cases h : Y = X <;> simp [h]
  simpa only [compatibleLotterySpace, Set.mem_setOf_eq, hsupp] using
    (compatible_singleton X)

end FairDivision.Topology
