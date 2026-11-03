import FairDivision.BF.PrimePowerIdenticalExistence
import FairDivision.BF.IdenticalExistence
import FairDivision.BF.PrimePowerHeterogeneousExistence

/-!
# Principal BF existence certificates: Sections 3–5

Reader entry point for the three principal existence results of the
Balanced Fair Division manuscript. Agent counts are stated directly
as n; the prime-power predicate includes a prime base and a positive exponent.
All item counts, including zero, are covered. Original valuations are arbitrary
real-valued functions on bundles, with no additivity, sign, normalization, or
monotonicity hypothesis. The same allocation has every displayed property.

Review these theorem types and the definitions in `Definitions.lean` that
interpret them. Intermediate topological statements and proof agreement with
the manuscript are not an additional semantic-review obligation.

These exports are covered by the successful certificate build and endpoint
axiom audit. Applications and swaps have their own reader facades.
-/

set_option autoImplicit false

namespace FairDivision.BF.MainTheorems

open FairDivision

/-- Section 3, `thm:identical-prime-power`: the common-threshold conclusion
and its EF[1,1] consequence hold for the SAME balanced complete allocation. -/
theorem identical_prime_power_common_threshold (n m : ℕ)
    (hn : IsPrimePowerAgentCount n) (v : Finset (Fin m)→ℝ) :
    ∃(A : Allocation n m)(t : ℝ),
      IsBalanced A ∧ HasCommonThreshold v A t ∧ IsEF11 (fun _=>v) A := by
  rcases hn with ⟨p,rank,hPrime,hPositive,rfl⟩
  letI : Fact p.Prime:=⟨hPrime⟩
  obtain ⟨A,t,hBalanced,hThreshold⟩:=
    FairDivision.BF.identical_primePower_exists_balanced_commonThreshold p rank m v
  exact ⟨A,t,hBalanced,hThreshold,hasCommonThreshold_implies_ef11 v A t hThreshold⟩

/-- The EF[1,1]-only statement of the Section 3 consequence, with n directly
in the type rather than a choice of its prime-power presentation. -/
theorem identical_prime_power_ef11 (n m : ℕ)
    (hn : IsPrimePowerAgentCount n) (v : Finset (Fin m)→ℝ) :
    ∃A : Allocation n m,IsBalanced A ∧ IsEF11 (fun _=>v) A := by
  obtain ⟨A,t,hBalanced,hThreshold,hFair⟩:=identical_prime_power_common_threshold n m hn v
  exact ⟨A,hBalanced,hFair⟩

/-- Section 4, `thm:identical-all-n`: every POSITIVE number of identical-
valuation agents, every item count, and the SAME common-threshold/EF[1,1]
allocation. This includes n=1. -/
theorem identical_common_threshold (n m : ℕ) (hn : 0<n)
    (v : Finset (Fin m)→ℝ) :
    ∃(A : Allocation n m)(t : ℝ),
      IsBalanced A ∧ HasCommonThreshold v A t ∧ IsEF11 (fun _=>v) A := by
  obtain ⟨A,t,hBalanced,hThreshold⟩:=
    FairDivision.BF.identical_exists_balanced_commonThreshold n m hn v
  exact ⟨A,t,hBalanced,hThreshold,hasCommonThreshold_implies_ef11 v A t hThreshold⟩

/-- The EF[1,1] consequence for arbitrary positive n and all m. -/
theorem identical_ef11 (n m : ℕ) (hn : 0<n) (v : Finset (Fin m)→ℝ) :
    ∃A : Allocation n m,IsBalanced A ∧ IsEF11 (fun _=>v) A :=
  FairDivision.BF.identical_exists_balanced_ef11 n m hn v

/-- Section 5, `thm:heterogeneous-all-m`: arbitrary independent bundle
valuations at any prime-power agent count, stated directly as n. -/
theorem heterogeneous_prime_power_ef11 (n m : ℕ)
    (hn : IsPrimePowerAgentCount n) (v : Fin n→Finset (Fin m)→ℝ) :
    ∃A : Allocation n m,IsBalanced A ∧ IsEF11 v A := by
  rcases hn with ⟨p,rank,hPrime,hPositive,rfl⟩
  letI : Fact p.Prime:=⟨hPrime⟩
  exact FairDivision.BF.heterogeneous_primePower_exists_balanced_ef11 p rank m v

/-- The harmless one-agent case is explicit. It does not change the paper's
positive-exponent definition of a prime-power agent count. -/
theorem heterogeneous_one_ef11 (m : ℕ) (v : Fin 1→Finset (Fin m)→ℝ) :
    ∃A : Allocation 1 m,IsBalanced A ∧ IsEF11 v A :=
  FairDivision.BF.heterogeneous_one_exists_balanced_ef11 m v

/-- Optional inclusive facade: the exact prime-power regime together with
its elementary n=1 boundary case, all stated on the original agent type. -/
theorem heterogeneous_one_or_prime_power_ef11 (n m : ℕ)
    (hn : n=1 ∨ IsPrimePowerAgentCount n) (v : Fin n→Finset (Fin m)→ℝ) :
    ∃A : Allocation n m,IsBalanced A ∧ IsEF11 v A := by
  rcases hn with rfl|hPrimePower
  · exact heterogeneous_one_ef11 m v
  · exact heterogeneous_prime_power_ef11 n m hPrimePower v

end FairDivision.BF.MainTheorems
