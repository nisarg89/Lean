import FairDivision.BF.Applications.DensitySharpnessGraphs
import FairDivision.Finite.ProjectedAllocation
import FairDivision.Finite.BalancedExistence

/-! The exact balanced-size bookkeeping for the manuscript's sharp examples.
Completeness supplies the number of large parts; no graph theorem is used. -/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.Applications

open FairDivision
open scoped BigOperators Classical

/-- At order kr+s, the existing floor/ceiling notion gives sizes r or r+1. -/
theorem density_balanced_size_cases {k m r s : ℕ} (hk : 0<k) (hs : s<k)
    (hCount : m=k*r+s) {A : Allocation k m} (hA : IsBalanced A) :
    ∀i : Fin k,(bundle A i).card=r ∨ (bundle A i).card=r+1 := by
  have hFloor : m/k=r := by
    rw [hCount,Nat.mul_add_div hk r s,Nat.div_eq_of_lt hs,Nat.add_zero]
  have hMod : m%k=s := by rw [hCount,Nat.mul_add_mod,Nat.mod_eq_of_lt hs]
  intro i
  rcases hA i with hi|hi
  · exact Or.inl (hi.trans hFloor)
  · by_cases hZero : s=0
    · exact Or.inl (by simpa [upperSize,hFloor,hMod,hZero] using hi)
    · exact Or.inr (by simpa [upperSize,hFloor,hMod,hZero] using hi)

/-- Some small part exists because the remainder is strictly below k. -/
theorem density_exists_small_part {k m r s : ℕ} (hk : 0<k) (hs : s<k)
    (hCount : m=k*r+s) {A : Allocation k m} (hA : IsBalanced A) :
    ∃i : Fin k,(bundle A i).card=r := by
  by_contra hNo
  push_neg at hNo
  have hAll : ∀i : Fin k,(bundle A i).card=r+1 :=
    fun i=>(density_balanced_size_cases hk hs hCount hA i).resolve_left (hNo i)
  have hSum:=sum_bundle_card A
  simp only [hAll,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hSum
  nlinarith

/-- A positive remainder forces a large part. -/
theorem density_exists_large_part {k m r s : ℕ} (hk : 0<k) (hs : 0<s) (hsk : s<k)
    (hCount : m=k*r+s) {A : Allocation k m} (hA : IsBalanced A) :
    ∃i : Fin k,(bundle A i).card=r+1 := by
  by_contra hNo
  push_neg at hNo
  have hAll : ∀i : Fin k,(bundle A i).card=r :=
    fun i=>(density_balanced_size_cases hk hsk hCount hA i).resolve_right (hNo i)
  have hSum:=sum_bundle_card A
  simp only [hAll,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hSum
  omega

/-- With s≥2, a large part exists away from ANY distinguished owner. This is
why a clique part remains even when the isolate lies in a large part. -/
theorem density_exists_other_large_part {k m r s : ℕ}
    (hk : 0<k) (hs : 2 ≤ s) (hsk : s<k) (hCount : m=k*r+s)
    {A : Allocation k m} (hA : IsBalanced A) (i : Fin k) :
    ∃j : Fin k,j≠i ∧ (bundle A j).card=r+1 := by
  by_contra hNo
  push_neg at hNo
  have hEach : ∀j : Fin k,(bundle A j).card≤r+(if j=i then 1 else 0) := by
    intro j
    by_cases hji : j=i
    · subst j
      simp only [ite_true]
      rcases density_balanced_size_cases hk hsk hCount hA i with hi|hi <;> omega
    · simp only [if_neg hji,Nat.add_zero]
      exact le_of_eq ((density_balanced_size_cases hk hsk hCount hA j).resolve_right
        (hNo j hji))
  have hTotal : m≤k*r+1 := by
    calc
      m=∑j : Fin k,(bundle A j).card := (sum_bundle_card A).symm
      _≤∑j : Fin k,(r+(if j=i then 1 else 0)) := Finset.sum_le_sum (fun j _=>hEach j)
      _=k*r+1 := by simp [Finset.sum_add_distrib]
  omega

theorem density_exists_other_agent {k : ℕ} (hk : 2≤k) (i : Fin k) :
    ∃j : Fin k,j≠i := by
  by_cases hZero : i.val=0
  · refine ⟨⟨1,by omega⟩,?_⟩
    intro h
    have hValue : (1 : ℕ)=i.val:=
      congrArg (fun j : Fin k => j.val) h
    omega
  · refine ⟨⟨0,by omega⟩,?_⟩
    intro h
    have hValue : (0 : ℕ)=i.val:=
      congrArg (fun j : Fin k => j.val) h
    omega

/-- The owner of a distinguished vertex is the only part containing it. -/
theorem distinguished_vertex_owner {k m : ℕ} (A : Allocation k m) (z : Fin m) :
    z∈bundle A (A z) ∧ ∀j : Fin k,j≠A z→z∉bundle A j := by
  refine ⟨by simp [bundle],?_⟩
  intro j hj hz
  exact hj ((by simpa [bundle] using hz : A z=j).symm)

end FairDivision.BF.Applications
