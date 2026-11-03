import FairDivision.BF.ReplacementFairnessWitness
import FairDivision.BF.IdenticalExistence
import FairDivision.BF.PrimePowerHeterogeneousExistence

/-!
# Both replacement-fairness propositions, by the manuscript's stated proof

Original valuations are functions on q-item bundles only. The two extension
constructions preserve identical valuations exactly. Apply the existing BF
allocation theorem to the chosen extensions, use divisibility for exact part
size, and apply the corresponding already proved replacement witness lemma.
No allocation algorithm or fairness theorem is replaced here.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.ReplacementFairness

open FairDivision

private theorem quota_le_items {n m q : ℕ} (hn : 0<n) (hm : m=n*q) : q≤ m := by
  rw [hm]
  calc
    q=1*q := by simp
    _≤n*q := Nat.mul_le_mul_right q (by omega)

/-- Proposition `replacement-fairness`, identical valuations, every positive
agent count. The replacement affects only the envied bundle. -/
theorem identical_exists_enviedReplacement (n m q : ℕ)
    (hn : 0<n) (hq : 1≤q) (hm : m=n*q) (v : QBundle m q→ℝ) :
    ∃A : Allocation n m,IsBalanced A ∧ IsEnviedReplacement (fun _=>v) A := by
  have hqm:=quota_le_items hn hm
  obtain ⟨A,hBalanced,hFair⟩:=FairDivision.BF.identical_exists_balanced_ef11 n m hn
    (worstExtension hqm v)
  exact ⟨A,hBalanced,enviedReplacement_of_worst_ef11 hqm (fun _=>v) A
    (balanced_exact_size hn hm hBalanced) hFair⟩

/-- Proposition `replacement-fairness`, heterogeneous valuations and any
prime-power agent count. Only original q-item values are inputs. -/
theorem primePower_exists_enviedReplacement (p rank m q : ℕ) [Fact p.Prime]
    (hq : 1≤q) (hm : m=(p^rank)*q) (v : Fin (p^rank)→QBundle m q→ℝ) :
    ∃A : Allocation (p^rank) m,IsBalanced A ∧ IsEnviedReplacement v A := by
  have hn : 0<p^rank:=pow_pos (Fact.out : p.Prime).pos rank
  have hqm:=quota_le_items hn hm
  obtain ⟨A,hBalanced,hFair⟩:=FairDivision.BF.heterogeneous_primePower_exists_balanced_ef11 p rank m
    (fun i=>worstExtension hqm (v i))
  exact ⟨A,hBalanced,enviedReplacement_of_worst_ef11 hqm v A
    (balanced_exact_size hn hm hBalanced) hFair⟩

/-- Proposition `own-replacement-fairness`, identical valuations, every
positive agent count. The rival bundle is unchanged in the comparison. -/
theorem identical_exists_ownReplacement (n m q : ℕ)
    (hn : 0<n) (hq : 1≤q) (hm : m=n*q) (v : QBundle m q→ℝ) :
    ∃A : Allocation n m,IsBalanced A ∧ IsOwnReplacement (fun _=>v) A := by
  have hqm:=quota_le_items hn hm
  obtain ⟨A,hBalanced,hFair⟩:=FairDivision.BF.identical_exists_balanced_ef11 n m hn
    (bestExtension hqm v)
  exact ⟨A,hBalanced,ownReplacement_of_best_ef11 hqm (fun _=>v) A
    (balanced_exact_size hn hm hBalanced) hFair⟩

/-- Proposition `own-replacement-fairness`, heterogeneous valuations at any
prime-power count. The replacement item can come from any other bundle. -/
theorem primePower_exists_ownReplacement (p rank m q : ℕ) [Fact p.Prime]
    (hq : 1≤q) (hm : m=(p^rank)*q) (v : Fin (p^rank)→QBundle m q→ℝ) :
    ∃A : Allocation (p^rank) m,IsBalanced A ∧ IsOwnReplacement v A := by
  have hn : 0<p^rank:=pow_pos (Fact.out : p.Prime).pos rank
  have hqm:=quota_le_items hn hm
  obtain ⟨A,hBalanced,hFair⟩:=FairDivision.BF.heterogeneous_primePower_exists_balanced_ef11 p rank m
    (fun i=>bestExtension hqm (v i))
  exact ⟨A,hBalanced,ownReplacement_of_best_ef11 hqm v A
    (balanced_exact_size hn hm hBalanced) hFair⟩

end FairDivision.BF.ReplacementFairness
