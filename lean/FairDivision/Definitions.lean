import Mathlib

/-!
# Statements for balanced fair division

This file contains the shared definitions used to interpret the existence
theorems of the Balanced Fair Division manuscript. It imports only Mathlib and contains no proofs.
The paper-to-Lean review should focus on this file and the final theorem types.
-/

set_option autoImplicit false

namespace FairDivision

/-- A complete allocation assigns every item to exactly one agent. -/
abbrev Allocation (n m : ℕ) := Fin m → Fin n

/-- The bundle assigned to agent `i`. -/
def bundle {n m : ℕ} (A : Allocation n m) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun g => A g = i)

/-- The upper permitted bundle size: `⌈m/n⌉` when `n > 0`. -/
def upperSize (n m : ℕ) : ℕ :=
  m / n + if m % n = 0 then 0 else 1

/-- Every bundle has size `⌊m/n⌋` or `⌈m/n⌉`. -/
def IsBalanced {n m : ℕ} (A : Allocation n m) : Prop :=
  ∀ i : Fin n, (bundle A i).card = m / n ∨ (bundle A i).card = upperSize n m

/-- A deletion is optional and removes at most one member of the given bundle. -/
def CanDeleteOne {m : ℕ} (D B : Finset (Fin m)) : Prop :=
  D ⊆ B ∧ D.card ≤ 1

/-- A common threshold lies between values obtainable from every bundle by
independent optional deletions of at most one item. This expands the paper's
`L(A_i) ≤ t ≤ U(A_i)` without introducing `min` and `max` notation. -/
def HasCommonThreshold {n m : ℕ} (v : Finset (Fin m) → ℝ)
    (A : Allocation n m) (t : ℝ) : Prop :=
  ∀ i : Fin n,
    (∃ D : Finset (Fin m), CanDeleteOne D (bundle A i) ∧
      v (bundle A i \ D) ≤ t) ∧
    (∃ D : Finset (Fin m), CanDeleteOne D (bundle A i) ∧
      t ≤ v (bundle A i \ D))

/-- EF[1,1]: for every ordered pair, the envying agent may independently delete
at most one item from her own bundle and at most one from the other bundle.
Both resulting bundles are evaluated by the envying agent. -/
def IsEF11 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (A : Allocation n m) : Prop :=
  ∀ i j : Fin n,
    ∃ C G : Finset (Fin m),
      CanDeleteOne C (bundle A i) ∧ CanDeleteOne G (bundle A j) ∧
      v i (bundle A i \ C) ≥ v i (bundle A j \ G)

/-- The paper uses prime powers `p^k` with `p` prime and `k ≥ 1`. -/
def IsPrimePowerAgentCount (n : ℕ) : Prop :=
  ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ n = p ^ k

/-- The utility of an integral bundle under additive, possibly signed values. -/
def additiveValue {n m : ℕ} (v : Fin n → Fin m → ℝ)
    (i : Fin n) (B : Finset (Fin m)) : ℝ :=
  ∑ g ∈ B, v i g

/-- The same additive instance viewed as arbitrary bundle valuations. -/
def additiveAsBundleValue {n m : ℕ} (v : Fin n → Fin m → ℝ) :
    Fin n → Finset (Fin m) → ℝ :=
  fun i B => additiveValue v i B

/-- A complete balanced fractional allocation: nonnegative fractions, column
sum one, and each row sum between `⌊m/n⌋` and `⌊m/n⌋+1` inclusive. -/
def IsBalancedFractional {n m : ℕ} (x : Fin n → Fin m → ℝ) : Prop :=
  (∀ i g, 0 ≤ x i g) ∧
  (∀ g, ∑ i : Fin n, x i g = 1) ∧
  (∀ i : Fin n, ((m / n : ℕ) : ℝ) ≤ ∑ g : Fin m, x i g ∧
    (∑ g : Fin m, x i g) ≤ ((m / n : ℕ) : ℝ) + 1)

/-- Additive utility of a fractional bundle. -/
def fractionalValue {n m : ℕ} (v x : Fin n → Fin m → ℝ) (i : Fin n) : ℝ :=
  ∑ g : Fin m, x i g * v i g

/-- Fractional Pareto optimality relative to the *balanced* fractional
polytope. Every proposed improvement must be feasible in that polytope. -/
def IsConstrainedFPO {n m : ℕ} (v : Fin n → Fin m → ℝ)
    (A : Allocation n m) : Prop :=
  ∀ x : Fin n → Fin m → ℝ, IsBalancedFractional x →
    ¬ ((∀ i : Fin n,
         additiveValue v i (bundle A i) ≤ fractionalValue v x i) ∧
       ∃ i : Fin n,
         additiveValue v i (bundle A i) < fractionalValue v x i)

/-- Swap envy-freeness: if agent `i` envies `j`, one item from each bundle can
be exchanged so that `i` does not envy `j` *after both bundles change*. -/
def IsSwapEF {n m : ℕ} (v : Fin n → Fin m → ℝ)
    (A : Allocation n m) : Prop :=
  ∀ i j : Fin n,
    additiveValue v i (bundle A j) ≤ additiveValue v i (bundle A i) ∨
    ∃ h ∈ bundle A i, ∃ g ∈ bundle A j,
      additiveValue v i (insert g ((bundle A i).erase h)) ≥
        additiveValue v i (insert h ((bundle A j).erase g))

end FairDivision
