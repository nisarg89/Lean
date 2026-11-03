import FairDivision.BF.PrimePowerIdenticalExistence
import FairDivision.BF.IdenticalExistence
import FairDivision.BF.PrimePowerHeterogeneousExistence

/-!
# Balanced EF[1,1] existence

Principal existence results for the Balanced Fair Division manuscript,
with arbitrary real-valued bundle valuations and every item count.
-/

set_option autoImplicit false

namespace FairDivision.BF.MainTheorems

open FairDivision

/-- Auxiliary formulation of `thm:identical-prime-power`. -/
theorem identical_prime_power_common_threshold (n m : ℕ)
    (hn : IsPrimePowerAgentCount n) (v : Finset (Fin m)→ℝ) :
    ∃(A : Allocation n m)(t : ℝ),
      IsBalanced A ∧ HasCommonThreshold v A t ∧ IsEF11 (fun _=>v) A := by
  rcases hn with ⟨p,rank,hPrime,hPositive,rfl⟩
  letI : Fact p.Prime:=⟨hPrime⟩
  obtain ⟨A,t,hBalanced,hThreshold⟩:=
    FairDivision.BF.identical_primePower_exists_balanced_commonThreshold p rank m v
  exact ⟨A,t,hBalanced,hThreshold,hasCommonThreshold_implies_ef11 v A t hThreshold⟩

/-- Balanced EF[1,1] existence for identical valuations and prime-power agent counts. -/
theorem identical_prime_power_ef11 (n m : ℕ)
    (hn : IsPrimePowerAgentCount n) (v : Finset (Fin m)→ℝ) :
    ∃A : Allocation n m,IsBalanced A ∧ IsEF11 (fun _=>v) A := by
  obtain ⟨A,t,hBalanced,hThreshold,hFair⟩:=identical_prime_power_common_threshold n m hn v
  exact ⟨A,hBalanced,hFair⟩

/-- Auxiliary formulation of `thm:identical-all-n`. -/
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

/-- Balanced EF[1,1] existence for heterogeneous valuations and prime-power agent counts. -/
theorem heterogeneous_prime_power_ef11 (n m : ℕ)
    (hn : IsPrimePowerAgentCount n) (v : Fin n→Finset (Fin m)→ℝ) :
    ∃A : Allocation n m,IsBalanced A ∧ IsEF11 v A := by
  rcases hn with ⟨p,rank,hPrime,hPositive,rfl⟩
  letI : Fact p.Prime:=⟨hPrime⟩
  exact FairDivision.BF.heterogeneous_primePower_exists_balanced_ef11 p rank m v

/-- Balanced EF[1,1] existence for one agent. -/
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
