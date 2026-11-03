import FairDivision.BF.IdenticalExistence

/-!
# Balanced nonlinear discrepancy from the common threshold

These are the manuscript's direct deletion-value comparisons. The general
bound places every full bundle within L of the SAME threshold. Monotonicity
places every full bundle in one common interval of length L. No alternative
partitioning argument is used.
-/

set_option autoImplicit false

namespace FairDivision.BF.Applications

open FairDivision

/-- The manuscript's hypothesis: one fresh item changes a set value by at
most L, with no additivity, sign, or monotonicity assumption. -/
def SingleItemLipschitz {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (L : ℝ) : Prop :=
  ∀ S : Finset α, ∀ x : α, x ∉ S → |f (insert x S) - f S| ≤ L

/-- Pairwise value spread, without choosing minimum or maximum agents. -/
def HasValueSpreadAtMost {n m : ℕ} (f : Finset (Fin m) → ℝ)
    (A : Allocation n m) (B : ℝ) : Prop :=
  ∀ i j : Fin n, |f (bundle A i) - f (bundle A j)| ≤ B

/-- Optional deletion is either no change or exactly the fresh-item
comparison in the Lipschitz hypothesis. -/
theorem deletion_value_distance {m : ℕ} {f : Finset (Fin m) → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hf : SingleItemLipschitz f L)
    {B D : Finset (Fin m)} (hD : CanDeleteOne D B) :
    |f B - f (B \ D)| ≤ L := by
  classical
  by_cases hEmpty : D = ∅
  · simpa [hEmpty] using hL
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hSingleton : D = {x} := by
    ext y
    constructor
    · intro hy
      exact Finset.mem_singleton.mpr (Finset.card_le_one.mp hD.2 y hy x hx)
    · intro hy
      have hyx : y = x := Finset.mem_singleton.mp hy
      simpa only [hyx] using hx
  have hxB : x ∈ B := hD.1 hx
  simpa only [hSingleton, Finset.sdiff_singleton_eq_erase,
    Finset.insert_erase hxB] using hf (B.erase x) x (Finset.notMem_erase x B)

/-- The common threshold lies within L of each full bundle value. -/
theorem threshold_distance {n m : ℕ} {f : Finset (Fin m) → ℝ}
    {A : Allocation n m} {t L : ℝ} (h : HasCommonThreshold f A t)
    (hL : 0 ≤ L) (hf : SingleItemLipschitz f L) :
    ∀ i : Fin n, |f (bundle A i) - t| ≤ L := by
  intro i
  obtain ⟨⟨D, hD, hLow⟩, ⟨E, hE, hHigh⟩⟩ := h i
  have hDelLow := abs_le.mp (deletion_value_distance hL hf hD)
  have hDelHigh := abs_le.mp (deletion_value_distance hL hf hE)
  exact abs_le.mpr ⟨by linarith [hDelHigh.1], by linarith [hDelLow.2]⟩

/-- The manuscript's factor two is just the width of [t-L,t+L]. -/
theorem threshold_spread {n m : ℕ} {f : Finset (Fin m) → ℝ}
    {A : Allocation n m} {t L : ℝ} (h : HasCommonThreshold f A t)
    (hL : 0 ≤ L) (hf : SingleItemLipschitz f L) :
    HasValueSpreadAtMost f A (2 * L) := by
  intro i j
  have hi := abs_le.mp (threshold_distance h hL hf i)
  have hj := abs_le.mp (threshold_distance h hL hf j)
  exact abs_le.mpr ⟨by linarith [hi.1, hj.2], by linarith [hi.2, hj.1]⟩

/-- For a nondecreasing function the threshold is below every full value,
and each full value is at most L above it. -/
theorem threshold_monotone_interval {n m : ℕ}
    {f : Finset (Fin m) → ℝ} {A : Allocation n m} {t L : ℝ}
    (h : HasCommonThreshold f A t) (hL : 0 ≤ L)
    (hf : SingleItemLipschitz f L) (hMono : Monotone f) :
    ∀ i : Fin n, t ≤ f (bundle A i) ∧ f (bundle A i) ≤ t + L := by
  intro i
  obtain ⟨⟨D, hD, hLow⟩, ⟨E, _, hHigh⟩⟩ := h i
  have hDel := (abs_le.mp (deletion_value_distance hL hf hD)).2
  exact ⟨hHigh.trans (hMono Finset.sdiff_subset), by linarith⟩

/-- The manuscript's monotone improvement uses the SAME partition and
common threshold, in an interval of length L. -/
theorem threshold_monotone_spread {n m : ℕ}
    {f : Finset (Fin m) → ℝ} {A : Allocation n m} {t L : ℝ}
    (h : HasCommonThreshold f A t) (hL : 0 ≤ L)
    (hf : SingleItemLipschitz f L) (hMono : Monotone f) :
    HasValueSpreadAtMost f A L := by
  intro i j
  have hi := threshold_monotone_interval h hL hf hMono i
  have hj := threshold_monotone_interval h hL hf hMono j
  exact abs_le.mpr ⟨by linarith [hi.1, hj.2], by linarith [hi.2, hj.1]⟩

/-- Negation reverses the two deletion witnesses but retains the SAME
partition. This is the manuscript's reduction for nonincreasing functions. -/
theorem threshold_negate {n m : ℕ} {f : Finset (Fin m) → ℝ}
    {A : Allocation n m} {t : ℝ} (h : HasCommonThreshold f A t) :
    HasCommonThreshold (fun S => -f S) A (-t) := by
  intro i
  obtain ⟨⟨D, hD, hLow⟩, ⟨E, hE, hHigh⟩⟩ := h i
  exact ⟨⟨E, hE, neg_le_neg hHigh⟩, ⟨D, hD, neg_le_neg hLow⟩⟩

theorem singleItemLipschitz_negate {α : Type*} [DecidableEq α]
    {f : Finset α → ℝ} {L : ℝ} (hf : SingleItemLipschitz f L) :
    SingleItemLipschitz (fun S => -f S) L := by
  intro S x hx
  simpa only [neg_sub_neg, abs_sub_comm] using hf S x hx

/-- The nonincreasing conclusion follows by applying the monotone
comparison to -f, exactly as in the manuscript. -/
theorem threshold_antitone_spread {n m : ℕ}
    {f : Finset (Fin m) → ℝ} {A : Allocation n m} {t L : ℝ}
    (h : HasCommonThreshold f A t) (hL : 0 ≤ L)
    (hf : SingleItemLipschitz f L) (hAnti : Antitone f) :
    HasValueSpreadAtMost f A L := by
  have hNegMono : Monotone (fun S => -f S) := fun _ _ hST => neg_le_neg (hAnti hST)
  have hNeg := threshold_monotone_spread (threshold_negate h) hL (singleItemLipschitz_negate hf) hNegMono
  intro i j
  simpa only [neg_sub_neg, abs_sub_comm] using hNeg i j

/-- Balanced nonlinear discrepancy for every positive number of parts,
with the manuscript's factor two and arbitrary real-valued set function. -/
theorem exists_balanced_nonlinear_discrepancy (k m : ℕ) (hk : 0 < k)
    (f : Finset (Fin m) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : SingleItemLipschitz f L) :
    ∃ A : Allocation k m, IsBalanced A ∧ HasValueSpreadAtMost f A (2 * L) := by
  obtain ⟨A, t, hBalanced, hThreshold⟩ :=
    identical_exists_balanced_commonThreshold k m hk f
  exact ⟨A, hBalanced, threshold_spread hThreshold hL hf⟩

/-- The sharp monotone constant, keeping balanced cardinalities. -/
theorem exists_balanced_monotone_discrepancy (k m : ℕ) (hk : 0 < k)
    (f : Finset (Fin m) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : SingleItemLipschitz f L) (hMono : Monotone f) :
    ∃ A : Allocation k m, IsBalanced A ∧ HasValueSpreadAtMost f A L := by
  obtain ⟨A, t, hBalanced, hThreshold⟩ :=
    identical_exists_balanced_commonThreshold k m hk f
  exact ⟨A, hBalanced, threshold_monotone_spread hThreshold hL hf hMono⟩

/-- Nonincreasing functions have the SAME sharp constant as nondecreasing
ones, by the manuscript's explicit negation argument. -/
theorem exists_balanced_antitone_discrepancy (k m : ℕ) (hk : 0 < k)
    (f : Finset (Fin m) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : SingleItemLipschitz f L) (hAnti : Antitone f) :
    ∃ A : Allocation k m, IsBalanced A ∧ HasValueSpreadAtMost f A L := by
  obtain ⟨A, t, hBalanced, hThreshold⟩ :=
    identical_exists_balanced_commonThreshold k m hk f
  exact ⟨A, hBalanced, threshold_antitone_spread hThreshold hL hf hAnti⟩

end FairDivision.BF.Applications
