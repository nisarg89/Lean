import FairDivision.Basic

/-!
# Instances with at most one item per agent

When the item count does not exceed the agent count, inject items into agents.
Every bundle has size at most one, so deleting the whole bundle leaves the
empty set on both sides of every fairness comparison.
-/

set_option autoImplicit false

namespace FairDivision

/-- Assign item `g` to agent with the same index. -/
def injectiveAllocation {n m : ℕ} (hm : m ≤ n) : Allocation n m :=
  fun g => ⟨g.val, lt_of_lt_of_le g.isLt hm⟩

private theorem injectiveAllocation_injective {n m : ℕ} (hm : m ≤ n) :
    Function.Injective (injectiveAllocation hm) := by
  intro g h heq
  exact Fin.ext (congrArg (fun z : Fin n => z.val) heq)

/-- An injective owner map has bundles of at most one item. -/
theorem bundle_card_le_one_of_injective {n m : ℕ} (A : Allocation n m)
    (hA : Function.Injective A) (i : Fin n) : (bundle A i).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro g hg h hh
  apply hA
  have hgi : A g = i := (Finset.mem_filter.mp hg).2
  have hhi : A h = i := (Finset.mem_filter.mp hh).2
  exact hgi.trans hhi.symm

/-- An allocation with bundles of at most one item has the common threshold
`v(∅)` for every arbitrary common valuation. -/
theorem commonThreshold_of_bundle_card_le_one {n m : ℕ}
    (v : Finset (Fin m) → ℝ) (A : Allocation n m)
    (hA : ∀ i : Fin n, (bundle A i).card ≤ 1) :
    HasCommonThreshold v A (v ∅) := by
  intro i
  refine ⟨⟨bundle A i, ⟨Finset.Subset.rfl, hA i⟩, ?_⟩,
    ⟨bundle A i, ⟨Finset.Subset.rfl, hA i⟩, ?_⟩⟩
  · simp
  · simp

/-- The same small-bundle observation yields EF[1,1] for heterogeneous
valuations without any monotonicity or normalization assumption. -/
theorem ef11_of_bundle_card_le_one {n m : ℕ}
    (v : Fin n → Finset (Fin m) → ℝ) (A : Allocation n m)
    (hA : ∀ i : Fin n, (bundle A i).card ≤ 1) : IsEF11 v A := by
  intro i j
  refine ⟨bundle A i, bundle A j,
    ⟨Finset.Subset.rfl, hA i⟩, ⟨Finset.Subset.rfl, hA j⟩, ?_⟩
  simp

/-- The injection allocation is balanced whenever `m ≤ n` and `n > 0`. -/
theorem injectiveAllocation_balanced {n m : ℕ} (hn : 0 < n) (hm : m ≤ n) :
    IsBalanced (injectiveAllocation hm) := by
  rcases lt_or_eq_of_le hm with hlt | heq
  · by_cases hz : m = 0
    · subst m
      exact isBalanced_zero hn (injectiveAllocation hm)
    · have hdiv : m / n = 0 := Nat.div_eq_of_lt hlt
      have hmod : m % n = m := Nat.mod_eq_of_lt hlt
      have hup : upperSize n m = 1 := by
        simp [upperSize, hdiv, hmod, hz]
      intro i
      have hcard := bundle_card_le_one_of_injective
        (injectiveAllocation hm) (injectiveAllocation_injective hm) i
      rcases Nat.eq_zero_or_pos (bundle (injectiveAllocation hm) i).card with hzero | hpos
      · left
        simpa [hdiv] using hzero
      · right
        have : (bundle (injectiveAllocation hm) i).card = 1 := by omega
        simpa [hup] using this
  · subst m
    intro i
    left
    have hi : i ∈ bundle (injectiveAllocation hm) i := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hpos : 0 < (bundle (injectiveAllocation hm) i).card :=
      Finset.card_pos.mpr ⟨i, hi⟩
    have hle := bundle_card_le_one_of_injective
      (injectiveAllocation hm)
      (injectiveAllocation_injective hm) i
    have hcard : (bundle (injectiveAllocation hm) i).card = 1 := by
      omega
    simpa [Nat.div_self hn] using hcard

/-- The identical-valuation theorem is proved for all `m ≤ n`. -/
theorem identical_small {n m : ℕ} (hn : 0 < n) (hm : m ≤ n)
    (v : Finset (Fin m) → ℝ) :
    ∃ (A : Allocation n m) (t : ℝ),
      IsBalanced A ∧ HasCommonThreshold v A t := by
  refine ⟨injectiveAllocation hm, v ∅,
    injectiveAllocation_balanced hn hm, ?_⟩
  exact commonThreshold_of_bundle_card_le_one v _
    (fun i => bundle_card_le_one_of_injective _ (injectiveAllocation_injective hm) i)

/-- The heterogeneous-valuation theorem is proved for all `m ≤ n`. -/
theorem heterogeneous_small {n m : ℕ} (hn : 0 < n) (hm : m ≤ n)
    (v : Fin n → Finset (Fin m) → ℝ) :
    ∃ A : Allocation n m, IsBalanced A ∧ IsEF11 v A := by
  refine ⟨injectiveAllocation hm, injectiveAllocation_balanced hn hm, ?_⟩
  exact ef11_of_bundle_card_le_one v _
    (fun i => bundle_card_le_one_of_injective _ (injectiveAllocation_injective hm) i)

end FairDivision
