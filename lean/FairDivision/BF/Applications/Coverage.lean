import FairDivision.BF.Applications.DiscrepancySharpness

/-!
# Sparse coverage with balanced cardinalities

Coverage is nondecreasing and changes by at most the number of elements
covered by the added item. The sharp example has one distinguished item
covering t elements and every other item covering nothing. The final
incidence computation expresses coverage and cardinality as two groups of
hit sets and proves the manuscript's sparsity t+1 comparison exactly.
-/

set_option autoImplicit false

namespace FairDivision.BF.Applications

open FairDivision

/-- The finite union of the elements covered by a bundle. -/
def coveredElements {m : ℕ} {β : Type*} [DecidableEq β]
    (U : Fin m → Finset β) (S : Finset (Fin m)) : Finset β := S.biUnion U

/-- The real-valued coverage valuation used in the discrepancy theorem. -/
def coverageValue {m : ℕ} {β : Type*} [DecidableEq β]
    (U : Fin m → Finset β) (S : Finset (Fin m)) : ℝ :=
  (coveredElements U S).card

theorem coveredElements_mono {m : ℕ} {β : Type*} [DecidableEq β]
    (U : Fin m → Finset β) : Monotone (coveredElements U) := by
  intro S T hST u hu
  obtain ⟨x, hx, hux⟩ := Finset.mem_biUnion.mp hu
  exact Finset.mem_biUnion.mpr ⟨x, hST hx, hux⟩

theorem coverageValue_monotone {m : ℕ} {β : Type*} [DecidableEq β]
    (U : Fin m → Finset β) : Monotone (coverageValue U) := by
  intro S T hST
  change ((coveredElements U S).card : ℝ) ≤ ((coveredElements U T).card : ℝ)
  exact_mod_cast Finset.card_le_card (coveredElements_mono U hST)

/-- Adding one item can introduce at most its own covered elements. -/
theorem coverageValue_lipschitz {m : ℕ} {β : Type*} [DecidableEq β]
    (U : Fin m → Finset β) (t : ℕ) (hU : ∀ x, (U x).card ≤ t) :
    SingleItemLipschitz (coverageValue U) (t : ℝ) := by
  intro S x _
  have hUnion : coveredElements U (insert x S) = U x ∪ coveredElements U S :=
    Finset.biUnion_insert
  have hLowerNat : (coveredElements U S).card ≤
      (coveredElements U (insert x S)).card :=
    Finset.card_le_card (coveredElements_mono U (Finset.subset_insert x S))
  have hUpperNat : (coveredElements U (insert x S)).card ≤
      (coveredElements U S).card + t := by
    rw [hUnion]
    have h := Finset.card_union_le (U x) (coveredElements U S)
    have hxSize : (U x).card ≤ t := hU x
    omega
  have hLower : coverageValue U S ≤ coverageValue U (insert x S) := by
    change ((coveredElements U S).card : ℝ) ≤
      ((coveredElements U (insert x S)).card : ℝ)
    exact_mod_cast hLowerNat
  have hUpper : coverageValue U (insert x S) ≤ coverageValue U S + (t : ℝ) := by
    change ((coveredElements U (insert x S)).card : ℝ) ≤
      ((coveredElements U S).card : ℝ) + (t : ℝ)
    exact_mod_cast hUpperNat
  rw [abs_of_nonneg (sub_nonneg.mpr hLower)]
  linarith

/-- The manuscript's coverage corollary, with arbitrary finite coverage
sets and every positive number of parts. -/
theorem exists_balanced_sparse_coverage (k m : ℕ) (hk : 0 < k)
    {β : Type*} [DecidableEq β] (U : Fin m → Finset β)
    (t : ℕ) (hU : ∀ x, (U x).card ≤ t) :
    ∃ A : Allocation k m, IsBalanced A ∧
      HasValueSpreadAtMost (coverageValue U) A (t : ℝ) :=
  exists_balanced_monotone_discrepancy k m hk (coverageValue U) t
    (Nat.cast_nonneg t) (coverageValue_lipschitz U t hU) (coverageValue_monotone U)

/-- Balanced cardinalities have spread at most one. -/
theorem balanced_cardinality_spread {k m : ℕ} {A : Allocation k m}
    (hBalanced : IsBalanced A) :
    HasValueSpreadAtMost (fun S : Finset (Fin m) => (S.card : ℝ)) A 1 := by
  have hUpper : upperSize k m ≤ m / k + 1 := by
    unfold upperSize
    split_ifs <;> omega
  have hLower : m / k ≤ upperSize k m := by
    unfold upperSize
    split_ifs <;> omega
  have hBounds (i : Fin k) :
      ((m / k : ℕ) : ℝ) ≤ ((bundle A i).card : ℝ) ∧
      ((bundle A i).card : ℝ) ≤ ((m / k : ℕ) : ℝ) + 1 := by
    have hNat : m / k ≤ (bundle A i).card ∧ (bundle A i).card ≤ m / k + 1 := by
      rcases hBalanced i with hi | hi <;> omega
    constructor
    · exact_mod_cast hNat.1
    · exact_mod_cast hNat.2
  intro i j
  have hi := hBounds i
  have hj := hBounds j
  exact abs_le.mpr ⟨by linarith [hi.1, hj.2], by linarith [hi.2, hj.1]⟩

/-- Both spreads asserted for the coverage/cardinality pair are attained
by the SAME balanced partition. -/
theorem exists_coverage_cardinality_pair (k m : ℕ) (hk : 0 < k)
    {β : Type*} [DecidableEq β] (U : Fin m → Finset β)
    (t : ℕ) (hU : ∀ x, (U x).card ≤ t) :
    ∃ A : Allocation k m, IsBalanced A ∧
      HasValueSpreadAtMost (coverageValue U) A (t : ℝ) ∧
      HasValueSpreadAtMost (fun S : Finset (Fin m) => (S.card : ℝ)) A 1 := by
  obtain ⟨A, hBalanced, hCoverage⟩ := exists_balanced_sparse_coverage k m hk U t hU
  exact ⟨A, hBalanced, hCoverage, balanced_cardinality_spread hBalanced⟩

/-- Exactly one distinguished item covers all t elements. -/
def distinguishedCoverage {m : ℕ} (g : Fin m) (t : ℕ) : Fin m → Finset (Fin t) :=
  fun x => if x = g then Finset.univ else ∅

theorem distinguishedCoverage_size {m : ℕ} (g : Fin m) (t : ℕ) (x : Fin m) :
    (distinguishedCoverage g t x).card ≤ t := by
  by_cases hx : x = g <;> simp [distinguishedCoverage, hx]

/-- A bundle has coverage t precisely when it contains the distinguished
item; otherwise its coverage is zero. -/
theorem distinguishedCoverage_value {m : ℕ} (g : Fin m) (t : ℕ)
    (S : Finset (Fin m)) :
    coverageValue (distinguishedCoverage g t) S = if g ∈ S then (t : ℝ) else 0 := by
  classical
  by_cases hg : g ∈ S
  · have hUnion : coveredElements (distinguishedCoverage g t) S = Finset.univ := by
      ext u
      constructor
      · intro _
        exact Finset.mem_univ _
      · intro _
        exact Finset.mem_biUnion.mpr ⟨g, hg, by simp [distinguishedCoverage]⟩
    simp [coverageValue, hUnion, hg]
  · have hUnion : coveredElements (distinguishedCoverage g t) S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      obtain ⟨x, hx, hux⟩ := Finset.mem_biUnion.mp hu
      by_cases hxg : x = g
      · exact hg (hxg ▸ hx)
      · simpa [distinguishedCoverage, hxg] using hux
    simp [coverageValue, hUnion, hg]

/-- In every partition into at least two parts, the distinguished item's
part has coverage t and another part has coverage zero. -/
theorem coverage_constant_sharp {k m : ℕ} (hk : 2 ≤ k)
    (g : Fin m) (t : ℕ) (A : Allocation k m) :
    ∃ i j : Fin k,
      |coverageValue (distinguishedCoverage g t) (bundle A i) -
        coverageValue (distinguishedCoverage g t) (bundle A j)| = (t : ℝ) := by
  let zero : Fin k := ⟨0, by omega⟩
  let one : Fin k := ⟨1, by omega⟩
  have hDistinct : zero ≠ one := by
    intro hEqual
    have hValue := congrArg Fin.val hEqual
    norm_num [zero, one] at hValue
  let j : Fin k := if A g = zero then one else zero
  have hOther : A g ≠ j := by
    by_cases hOwner : A g = zero
    · simpa only [j, if_pos hOwner, hOwner] using hDistinct
    · simpa only [j, if_neg hOwner] using hOwner
  have hi : g ∈ bundle A (A g) := by simp [bundle]
  have hj : g ∉ bundle A j := by simpa [bundle] using hOther
  refine ⟨A g, j, ?_⟩
  simp [distinguishedCoverage_value, hi, hj, abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) t)]

/-- Sharpness persists for EVERY positive multiple of the number of
parts. Every balanced part in this example has exactly r items. -/
theorem coverage_sharp_equal_parts (k r t : ℕ) (hk : 2 ≤ k) (hr : 0 < r) :
    ∃ (U : Fin (k * r) → Finset (Fin t)) (A : Allocation k (k * r)),
      (∀ x, (U x).card ≤ t) ∧ IsBalanced A ∧
      (∀ i : Fin k, (bundle A i).card = r) ∧
      ∃ i j : Fin k, |coverageValue U (bundle A i) - coverageValue U (bundle A j)| =
        (t : ℝ) := by
  have hkPos : 0 < k := by omega
  let g : Fin (k * r) := ⟨0, Nat.mul_pos hkPos hr⟩
  let U := distinguishedCoverage g t
  obtain ⟨A, hBalanced, _⟩ := exists_balanced_sparse_coverage k (k * r) hkPos U t
    (distinguishedCoverage_size g t)
  refine ⟨U, A, distinguishedCoverage_size g t, hBalanced, ?_,
    coverage_constant_sharp hk g t A⟩
  intro i
  have hDiv : k * r / k = r := Nat.mul_div_cancel_left r hkPos
  have hMod : k * r % k = 0 := Nat.mod_eq_zero_of_dvd ⟨r, rfl⟩
  rcases hBalanced i with hi | hi
  · simpa only [hDiv] using hi
  · simpa [upperSize, hDiv, hMod] using hi

/-- Coverage elements index the hit sets {x : u ∈ U_x}; singleton hit sets
supply the second function, cardinality. Distinct labels are retained even
when two hit sets happen to coincide. -/
def coverageCardinalityFamily {m : ℕ} {β : Type*} [DecidableEq β]
    (U : Fin m → Finset β) : β ⊕ Fin m → Finset (Fin m)
  | Sum.inl u => Finset.univ.filter (fun x => u ∈ U x)
  | Sum.inr x => {x}

/-- The elements whose coverage hit sets are hit by S are exactly its
covered elements. -/
theorem coverage_hit_set_representation {m : ℕ} {β : Type*}
    [Fintype β] [DecidableEq β] (U : Fin m → Finset β) (S : Finset (Fin m)) :
    Finset.univ.filter
      (fun u : β => (S ∩ coverageCardinalityFamily U (Sum.inl u)).Nonempty) =
      coveredElements U S := by
  ext u
  simp [coverageCardinalityFamily, coveredElements, Finset.Nonempty]

/-- The singleton hit sets hit by S are exactly its members, so their
number is its cardinality. -/
theorem cardinality_hit_set_representation {m : ℕ} {β : Type*} [DecidableEq β]
    (U : Fin m → Finset β) (S : Finset (Fin m)) :
    Finset.univ.filter
      (fun x : Fin m => (S ∩ coverageCardinalityFamily U (Sum.inr x)).Nonempty) = S := by
  ext x
  simp [coverageCardinalityFamily, Finset.Nonempty]

/-- An item's family incidences are its covered elements plus exactly its
own singleton label. This is the explicit family-model sparsity count. -/
theorem coverage_cardinality_incidence {m : ℕ} {β : Type*}
    [Fintype β] [DecidableEq β] (U : Fin m → Finset β) (x : Fin m) :
    Finset.univ.filter (fun z : β ⊕ Fin m => x ∈ coverageCardinalityFamily U z) =
      (U x).disjSum {x} := by
  ext z
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  cases z <;> simp [coverageCardinalityFamily,eq_comm]

/-- The pair consisting of coverage and cardinality has sparsity at most
t+1, exactly as claimed in the manuscript's family-model comparison. -/
theorem coverage_cardinality_sparsity {m : ℕ} {β : Type*}
    [Fintype β] [DecidableEq β] (U : Fin m → Finset β)
    (t : ℕ) (hU : ∀ x, (U x).card ≤ t) :
    ∀ x : Fin m,
      (Finset.univ.filter
        (fun z : β ⊕ Fin m => x ∈ coverageCardinalityFamily U z)).card ≤ t + 1 := by
  intro x
  rw [coverage_cardinality_incidence, Finset.card_disjSum, Finset.card_singleton]
  exact Nat.add_le_add_right (hU x) 1

end FairDivision.BF.Applications
