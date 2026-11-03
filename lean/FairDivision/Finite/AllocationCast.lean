import FairDivision.Definitions

/-!
# Transport of finite-item allocations across equal item counts

This is bookkeeping for the final BF padding proof. When two natural-number
expressions for the real item count are equal, an allocation and valuation
can be transported across the corresponding `Fin` types without changing
balancedness or the one-deletion common-threshold property.
-/

set_option autoImplicit false

namespace FairDivision.Finite

open FairDivision

/-- Rename the item type of an allocation along an equality of counts. -/
def castAllocation {n m k : ℕ} (h : m = k)
    (A : Allocation n m) : Allocation n k :=
  h ▸ A

/-- Pull a valuation on `k` items back to `m` items along an equality. -/
def castValuation {m k : ℕ} (h : m = k)
    (v : Finset (Fin k) → ℝ) : Finset (Fin m) → ℝ :=
  h.symm ▸ v

/-- Renaming an item type preserves balancedness. -/
theorem castAllocation_balanced {n m k : ℕ} (h : m = k)
    (A : Allocation n m) (hA : IsBalanced A) :
    IsBalanced (castAllocation h A) := by
  cases h
  simpa [castAllocation] using hA

/-- Renaming an item type preserves a common optional-deletion threshold. -/
theorem castAllocation_commonThreshold {n m k : ℕ} (h : m = k)
    (v : Finset (Fin k) → ℝ) (A : Allocation n m) (t : ℝ)
    (hA : HasCommonThreshold (castValuation h v) A t) :
    HasCommonThreshold v (castAllocation h A) t := by
  cases h
  simpa [castAllocation, castValuation] using hA


/-- The same literal item-type renaming preserves EF[1,1] for arbitrary
heterogeneous bundle valuations. This is transport only; no new allocation
or fairness argument is performed. -/
theorem castAllocation_ef11 {n m k:ℕ} (h:m=k)
    (v:Fin n→Finset (Fin k)→ℝ) (A:Allocation n m)
    (hA:IsEF11 (fun i=>castValuation h (v i)) A):
    IsEF11 v (castAllocation h A):=by
  cases h
  simpa only [castAllocation,castValuation] using hA

end FairDivision.Finite
