import FairDivision.BF.MonotoneFairness
import FairDivision.BF.ReplacementFairnessWitness

/-!
# Full equal capacities and the exact feasible-subset comparison

Balancedness with nq items saturates the equal capacities. Restoring the
own-bundle deletion gives ordinary goods EF1. Comparing with all feasible
subsets of another bundle is then equivalent, exactly as explained in the
manuscript's applications appendix.
-/

set_option autoImplicit false

namespace FairDivision.BF.Applications

open FairDivision FairDivision.BF.ReplacementFairness

/-- Exact EF1 comparisons with every capacity-feasible rival subset. -/
def IsFeasibleGoodsEF1 {n m:ℕ} (q:ℕ) (v:Fin n→Finset (Fin m)→ℝ)
    (A:Allocation n m):Prop:=
  ∀i j:Fin n,∀F:Finset (Fin m),F⊆bundle A j→F.card≤q→
    ∃D:Finset (Fin m),CanDeleteOne D F ∧v i (F\D)≤v i (bundle A i)

/-- Ordinary EF1 implies the exact feasible-subset guarantee, using the
same witness when present in F and restoring it otherwise. -/
theorem goodsEF1_feasible {n m q:ℕ} {v:Fin n→Finset (Fin m)→ℝ}
    {A:Allocation n m} (hMono:∀i,Monotone (v i)) (hFair:IsGoodsEF1 v A):
    IsFeasibleGoodsEF1 q v A:=by
  intro i j F hF hCap
  obtain ⟨G,hG,hVal⟩:=hFair i j
  refine ⟨G∩F,⟨Finset.inter_subset_right,
    (Finset.card_le_card Finset.inter_subset_left).trans hG.2⟩,?_⟩
  have hSub:F\(G∩F)⊆bundle A j\G:=by
    intro x hx
    obtain ⟨hxF,hxNot⟩:=Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hF hxF,fun hxG=>hxNot (Finset.mem_inter.mpr ⟨hxG,hxF⟩)⟩
  exact (hMono i hSub).trans hVal

theorem feasible_goodsEF1 {n m q:ℕ} {v:Fin n→Finset (Fin m)→ℝ}
    {A:Allocation n m} (hCap:∀j,(bundle A j).card≤q)
    (hFair:IsFeasibleGoodsEF1 q v A):IsGoodsEF1 v A:=by
  intro i j
  exact hFair i j (bundle A j) Finset.Subset.rfl (hCap j)

/-- At full equal capacities the two exact fairness guarantees coincide. -/
theorem feasibleGoodsEF1_iff {n m q:ℕ} {v:Fin n→Finset (Fin m)→ℝ}
    {A:Allocation n m} (hMono:∀i,Monotone (v i)) (hCap:∀j,(bundle A j).card≤q):
    IsFeasibleGoodsEF1 q v A↔IsGoodsEF1 v A:=
  ⟨feasible_goodsEF1 hCap,goodsEF1_feasible hMono⟩

/-- `applications-capacities`, heterogeneous nondecreasing valuations,
prime-power agents, including capacity zero. -/
theorem primePower_exists_full_capacity_goodsEF1
    (p rank q:ℕ) [Fact p.Prime]
    (v:Fin (p^rank)→Finset (Fin ((p^rank)*q))→ℝ)
    (hMono:∀i,Monotone (v i)):
    ∃A:Allocation (p^rank) ((p^rank)*q),
      (∀i,(bundle A i).card=q) ∧IsGoodsEF1 v A ∧IsFeasibleGoodsEF1 q v A:=by
  obtain ⟨A,hBalance,hFair⟩:=heterogeneous_primePower_exists_balanced_ef11 p rank ((p^rank)*q) v
  have hn:0<p^rank:=pow_pos (Fact.out:p.Prime).pos rank
  have hGoods:IsGoodsEF1 v A:=fun i=>ef11_goodsEF1_for hFair i (hMono i)
  exact ⟨A,balanced_exact_size hn rfl hBalance,hGoods,goodsEF1_feasible hMono hGoods⟩

/-- `applications-capacities`, identical nondecreasing valuations,
every positive number of agents, including capacity zero. -/
theorem identical_exists_full_capacity_goodsEF1
    (n q:ℕ) (hn:0<n) (v:Finset (Fin (n*q))→ℝ) (hMono:Monotone v):
    ∃A:Allocation n (n*q),(∀i,(bundle A i).card=q) ∧
      IsGoodsEF1 (fun _=>v) A ∧IsFeasibleGoodsEF1 q (fun _=>v) A:=by
  obtain ⟨A,hBalance,hGoods⟩:=identical_exists_balanced_goodsEF1 n (n*q) hn v hMono
  exact ⟨A,balanced_exact_size hn rfl hBalance,hGoods,
    goodsEF1_feasible (fun _=>hMono) hGoods⟩

end FairDivision.BF.Applications
