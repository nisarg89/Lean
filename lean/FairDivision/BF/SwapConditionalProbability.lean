import FairDivision.BF.SwapMixedCount
import FairDivision.Probability.UnitUniformProduct

/-!
# The actual conditional probability bound for one fixed allocation

Condition on the n original bundle weights b. The remaining independent
Uniform(0,1) coordinates are z. The literal splice below retains b on the
original bundles and z on all other subsets. For injective b, orient each
unordered pair from its lower original weight to its higher one. Actual
mixed-set boxes are disjoint coordinate blocks and have probability at
least η(q)=2^(−(choose(2q,q)−2)). A t-swap allocation must avoid ALL boxes.

This is the manuscript's conditioning argument, with actual continuous
product measures and the original-item-subset coordinates retained.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.SwapConditionalProbability

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
open FairDivision.BF SwapObstruction
open FairDivision.Probability.UnitUniformProduct

variable {n m q t : ℕ}

/-- Positive equal-size bundles define distinct ORIGINAL noise coordinates. -/
theorem bundle_index_injective (A : Allocation n m) (hq : 0<q)
    (hSize : HasEqualBundleSize A q) : Function.Injective (bundle A) := by
  intro i j hEq
  obtain ⟨g,hg⟩:=Finset.card_pos.mp (show 0<(bundle A i).card by rw [hSize i];exact hq)
  have hgi : A g=i:=(Finset.mem_filter.mp hg).2
  have hgjMem : g∈bundle A j:=by
    rw [←hEq]
    exact hg
  have hgj : A g=j:=(Finset.mem_filter.mp hgjMem).2
  exact hgi.symm.trans hgj

/-- Actual conditioning splice. Unused copies of original coordinates in
z are harmless; all other coordinates keep their independent unit laws. -/
def realize (A : Allocation n m) (b : Fin n→ℝ)
    (z : Finset (Fin m)→ℝ) (U : Finset (Fin m)) : ℝ := by
  classical
  exact if h:∃i : Fin n,bundle A i=U then b h.choose else z U

@[simp] theorem realize_original (A : Allocation n m) (hq : 0<q)
    (hSize : HasEqualBundleSize A q) (b : Fin n→ℝ) (z : Finset (Fin m)→ℝ) (i : Fin n) :
    realize A b z (bundle A i)=b i := by
  classical
  have h : ∃j : Fin n,bundle A j=bundle A i:=⟨i,rfl⟩
  have hIndex : h.choose=i:=bundle_index_injective A hq hSize h.choose_spec
  simp only [realize,dif_pos h,hIndex]

theorem realize_mixed (A : Allocation n m) (b : Fin n→ℝ) (z : Finset (Fin m)→ℝ)
    (i j : Fin n) (hij : i≠j) (U : Finset (Fin m))
    (hMixed : Mixed q (bundle A i) (bundle A j) U) : realize A b z U=z U := by
  classical
  have hNot : ¬∃k : Fin n,bundle A k=U := by
    rintro ⟨k,hk⟩
    exact mixed_ne_original_bundle A i j hij U hMixed k hk.symm
  simp only [realize,dif_neg hNot]

/-- The orientation may depend on the fixed conditioning value b. -/
def oriented (b : Fin n→ℝ) (P : AgentPair n) : Fin n×Fin n :=
  if b (representatives P).1<b (representatives P).2 then representatives P
  else ((representatives P).2,(representatives P).1)

theorem oriented_spec (b : Fin n→ℝ) (P : AgentPair n) :
    (oriented b P).1≠(oriented b P).2 ∧
      P.1={(oriented b P).1,(oriented b P).2} := by
  unfold oriented
  split_ifs
  · exact representatives_spec P
  · exact ⟨(representatives_spec P).1.symm,by
      simpa only [Finset.pair_comm] using (representatives_spec P).2⟩

theorem oriented_envy (b : Fin n→ℝ) (hb : Function.Injective b) (P : AgentPair n) :
    b (oriented b P).1<b (oriented b P).2 := by
  have hDifferent : b (representatives P).1≠b (representatives P).2:=
    fun h=>(representatives_spec P).1 (hb h)
  unfold oriented
  split_ifs with h
  · exact h
  · exact lt_of_le_of_ne (le_of_not_gt h) hDifferent.symm

theorem oriented_block (A : Allocation n m) (b : Fin n→ℝ) (P : AgentPair n) :
    pairBlock (q:=q) A P=
      mixedFamily q (bundle A (oriented b P).1) (bundle A (oriented b P).2) := by
  unfold pairBlock oriented
  split_ifs
  · rfl
  · exact mixedFamily_comm _ _

/-- Actual half-interval prescriptions on the mixed coordinates. -/
def sides (A : Allocation n m) (b : Fin n→ℝ) (P : AgentPair n)
    (U : pairBlock (q:=q) A P) : Option Bool :=
  if q<2*(U.1∩bundle A (oriented b P).1).card then some false
  else if q<2*(U.1∩bundle A (oriented b P).2).card then some true else none

/-- These actual cylinder conditions imply precisely the oriented
manuscript obstruction on the realized valuation. -/
theorem box_obstruction (A : Allocation n m) (b : Fin n→ℝ)
    (P : AgentPair n) (z : Finset (Fin m)→ℝ)
    (hBox : (fun U : pairBlock (q:=q) A P=>z U)∈box (sides A b P)) :
    Obstruction q (realize A b z)
      (bundle A (oriented b P).1) (bundle A (oriented b P).2) := by
  classical
  let i:=(oriented b P).1
  let j:=(oriented b P).2
  have hij : i≠j:=(oriented_spec b P).1
  have hDisjoint:=allocation_bundle_disjoint A i j hij
  intro U hMixed
  have hMem : U∈pairBlock (q:=q) A P := by
    rw [oriented_block A b P]
    exact (mem_mixedFamily (q:=q) _ _ U).mpr hMixed
  have hCoordinate : z U∈interval (sides A b P ⟨U,hMem⟩):=hBox ⟨U,hMem⟩ (Set.mem_univ _)
  rw [realize_mixed A b z i j hij U hMixed]
  constructor
  · intro hMajority
    simpa only [sides,dif_pos,if_pos hMajority,interval,Set.mem_Iio] using hCoordinate
  · intro hMajority
    have hNotFirst : ¬q<2*(U∩bundle A (oriented b P).1).card :=
      fun h=>majority_incompatible _ _ U hDisjoint hMixed.2.1 ⟨h,hMajority⟩
    simpa only [sides,if_neg hNotFirst,if_pos hMajority,interval,Set.mem_Ioi] using hCoordinate

def eta (q : ℕ) : ℝ≥0∞:=((2 : ℝ≥0∞)⁻¹)^((2*q).choose q-2)

theorem eta_positive (q : ℕ) : 0<eta q:=by
  unfold eta
  have hBase : 0<(2 : ℝ≥0∞)⁻¹:=ENNReal.inv_pos.mpr (by norm_num)
  exact ENNReal.pow_pos hBase _

/-- The exact fixed-allocation conditional estimate. All randomness,
orientations, mixed coordinates and interval events are actual objects. -/
theorem conditional_fairness_bound (A : Allocation n m)
    (hThreshold : 2*t+1≤q) (hSize : HasEqualBundleSize A q)
    (b : Fin n→ℝ) (hb : Function.Injective b) :
    law (Finset (Fin m)) {z | IsTSwapEF t (fun _=>SwapPerturbedValuation.value q (realize A b z)) A}≤
      (1-eta q)^(n.choose 2) := by
  classical
  have hq : 0<q:=by omega
  have hSubset : {z | IsTSwapEF t
      (fun _=>SwapPerturbedValuation.value q (realize A b z)) A}⊆
      {z | ∀P : AgentPair n,(fun U : pairBlock (q:=q) A P=>z U)∉box (sides A b P)} := by
    intro z hFair P hBox
    let i:=(oriented b P).1
    let j:=(oriented b P).2
    have hEnvy : realize A b z (bundle A i)<realize A b z (bundle A j) := by
      rw [realize_original A hq hSize,realize_original A hq hSize]
      exact oriented_envy b hb P
    exact not_tSwapEF_of_obstruction hThreshold (realize A b z) A hSize i j hEnvy
      (box_obstruction A b P z hBox) hFair
  apply (measure_mono hSubset).trans
  have hCard (P : AgentPair n) : (pairBlock (q:=q) A P).card≤(2*q).choose q-2 := by
    have hCount : (pairBlock (q:=q) A P).card=(2*q).choose q-2 :=
      mixedFamily_card hq _ _
        (allocation_bundle_disjoint A _ _ (representatives_spec P).1) (hSize _) (hSize _)
    exact hCount.le
  have hBound:=avoid_disjoint_boxes_le (pairBlock (q:=q) A) (pairBlocks_disjoint A)
    (sides A b) ((2*q).choose q-2) hCard
  simpa only [eta,agentPair_card] using hBound

end FairDivision.BF.SwapConditionalProbability
