import FairDivision.BF.Recording.ReserveRelabel
import FairDivision.Finite.DisjointReserves

/-!
# Actual equitable child lotteries in disjoint parent pools

At a simultaneous zero, recover a zero of each SAME child recorder within
its outer pool. The existing aggregate dummy-reserve theorem assigns disjoint
actual reserves of exactly the needed maxima. Relabel only the used child
prefix into that reserve. This produces the actual child lotteries on the
parent's common item inventory, ready for their independent product.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace FairDivision.BF.Recording

open FairDivision.Topology FairDivision.Finite

/-- Actual common-inventory child lotteries, before their independent
product. All expected values use the original real bundle valuation. -/
structure ChildLotteryBank {p a q m:ℕ} (parent:Space (a*p) q m)
    (v:Finset (Fin m)→ℝ) (t:ℝ) where
  stock:Fin p→Finset (Fin (m+a*p))
  lottery:Fin p→stdSimplex ℝ (PartialVertex a (dummyLabels m (a*p)) (q-1) 1)
  compatible:∀i,lottery i∈compatibleLotterySpace a (m+a*p) (q-1) 1 (dummyLabels m (a*p))
  in_stock:∀i j,pool (lotterySupport (lottery i)) j⊆stock i
  stock_disjoint:∀i j:Fin p,i≠j→Disjoint (stock i) (stock j)
  stock_available:∀i,stock i⊆available parent
  equitable:∀i j,(∑X:PartialVertex a (dummyLabels m (a*p)) (q-1) 1,
    (lottery i).1 X*v (realPart (partialBundle X.1 j)))=t

/-- In the actual zero-dummy case every child's available stock is
purely real. This follows from its exact parent-pool inclusion, without
changing any ambient formal source inventory or choosing new labels. -/
theorem ChildLotteryBank.stock_disjoint_dummies_of_parentBudget_zero
    {p a q m:ℕ} {parent:Space (a*p) q m}
    {v:Finset (Fin m)→ℝ} {t:ℝ} (bank:ChildLotteryBank parent v t)
    (hZero:parentDummyBudget parent=0) (i:Fin p):
    Disjoint (bank.stock i) (dummyLabels m (a*p)):=by
  have hStock:bank.stock i⊆(parentRealStock parent).map (realEmbedding m (a*p)):=by
    have hAvailable:=bank.stock_available i
    rw [available_eq_parentStock,hZero,initialDummies_zero,Finset.union_empty] at hAvailable
    exact hAvailable
  exact (realImage_disjoint_dummies (parentRealStock parent)).mono_left hStock

/-- Actual simultaneous-zero recovery with the manuscript's precise
outer-pool and actual dummy-label guarantees. -/
theorem exists_childLotteryBank {p a q m:ℕ} (hp:2≤p) (ha:0<a)
    {v:Finset (Fin m)→ℝ}{L H:ℝ}{hLH:L≤H}
    (Φ:RecordingFunction a q m v L H hLH)
    (parent:Space (a*p) q m) (μ:stdSimplex ℝ (ChildProfile p a q m))
    (t:Set.Icc L H)
    (hFace:finiteSimplexSupport μ∈availableAuxiliaryComplex p a q m
      (parentRealStock parent) (parentDummyBudget parent))
    (hZero:∀i:Fin p,childScores Φ (μ,t) i=0):
    Nonempty (ChildLotteryBank parent v t.val):=by
  classical
  let S:=finiteSimplexSupport μ
  let E:Fin p→Finset (Fin m):=fun i=>childRealPool S i
  let d:Fin p→ℕ:=fun i=>childDummyMax S i
  have hA:0< m+a*p:=by have h:=Nat.mul_pos ha (by omega:0<p);omega
  have hParentCap:parentDummyBudget parent≤a*p:=by
    apply Finset.sup_le
    intro b hb
    exact dummyCount_le b
  have hCap:∀i:Fin p,d i≤a:=by
    intro i
    apply Finset.sup_le
    intro b hb
    exact dummyCount_le (b i)
  let D₀:=initialDummies m (a*p) (parentDummyBudget parent)
  have hD₀:D₀.card=parentDummyBudget parent:=card_initialDummies _ _ _ hParentCap
  obtain ⟨R,hRes,hPair⟩:=exists_disjoint_reserves (Finset.univ:Finset (Fin p)) D₀ d (by
    rw [hD₀]
    simpa using hFace.2.2.1)
  have hR:∀i:Fin p,R i⊆D₀ ∧(R i).card=d i:=fun i=>hRes i (Finset.mem_univ i)
  have hRGlobal:∀i:Fin p,R i⊆dummyLabels m (a*p):=
    fun i=>(hR i).1.trans (initialDummies_subset _ _ _)
  let stock:Fin p→Finset (Fin (m+a*p)):=fun i=>(E i).map (realEmbedding m (a*p))∪R i
  have hEach:∀i:Fin p,∃ν:stdSimplex ℝ (PartialVertex a (dummyLabels m (a*p)) (q-1) 1),
      ν∈compatibleLotterySpace a (m+a*p) (q-1) 1 (dummyLabels m (a*p)) ∧
      (∀j:Fin a,pool (lotterySupport ν) j⊆stock i) ∧
      ∀j:Fin a,(∑X:PartialVertex a (dummyLabels m (a*p)) (q-1) 1,
        ν.1 X*v (realPart (partialBundle X.1 j)))=t.val:=by
    intro i
    obtain ⟨x,hCertificate,hWithin⟩:=child_lottery_in_outer_pool Φ μ t i (hZero i)
    have hUsed:available x⊆reserveSourceStock (E i) (R i):=by
      simpa only [reserveSourceStock,(hR i).2] using hWithin
    let e:=reserveRelabel (a:=a) hA (R i)
    have hInject:Set.InjOn e (available x:Set (Fin (m+a))):=
      (reserveRelabel_injectiveOn_stock hA (E i) (R i) (hRGlobal i)).mono hUsed
    have hDummy:∀g∈available x,e g∈dummyLabels m (a*p)↔g∈dummyLabels m a:=by
      intro g hg
      exact reserveRelabel_dummy_iff_on_stock hA (E i) (R i) (hRGlobal i) g (hUsed hg)
    obtain ⟨ν,hν,hνPool,hνMean⟩:=hCertificate.relabel (dummyLabels m (a*p)) e hInject hDummy
      (fun B=>v (realPart B)) (by
        intro B hB
        rw [reserveRelabel_realPart hA (E i) (R i) (hRGlobal i) B (hB.trans hUsed)])
    refine ⟨ν,hν,?_,hνMean⟩
    intro j z hz
    obtain ⟨g,hg,rfl⟩:=Finset.mem_image.mp (hνPool j hz)
    exact reserveRelabel_maps_stock hA (E i) (R i) (hUsed hg)
  choose ν hCompatible hWithin hMean using hEach
  refine ⟨{
    stock:=stock
    lottery:=ν
    compatible:=hCompatible
    in_stock:=hWithin
    stock_disjoint:=?_
    stock_available:=?_
    equitable:=hMean }⟩
  ·intro i j hij
   apply Finset.disjoint_left.mpr
   intro z hzi hzj
   rcases Finset.mem_union.mp hzi with hRealI|hDummyI <;>
     rcases Finset.mem_union.mp hzj with hRealJ|hDummyJ
   ·exact (Finset.disjoint_left.mp
       ((Finset.disjoint_map (realEmbedding m (a*p))).mpr (hFace.2.1 i j hij))) hRealI hRealJ
   ·exact (Finset.disjoint_left.mp (realImage_disjoint_dummies (E i))) hRealI (hRGlobal j hDummyJ)
   ·exact (Finset.disjoint_left.mp (realImage_disjoint_dummies (E j))) hRealJ (hRGlobal i hDummyI)
   ·exact (Finset.disjoint_left.mp (hPair (Finset.mem_univ i) (Finset.mem_univ j) hij)) hDummyI hDummyJ
  ·intro i z hz
   rw [available_eq_parentStock]
   rcases Finset.mem_union.mp hz with hzReal|hzDummy
   ·refine Finset.mem_union_left _ ?_
    obtain ⟨g,hg,rfl⟩:=Finset.mem_map.mp hzReal
    exact Finset.mem_map.mpr ⟨g,hFace.2.2.2 i hg,rfl⟩
   ·exact Finset.mem_union_right _ ((hR i).1 hzDummy)

/-- The preceding bank is constructed at every zero of the ACTUAL child T.
No expected-score, child-zero or lottery runner premise remains. -/
theorem actualChildT_zero_childLotteryBank {p a q m:ℕ}
    (hp:2≤p) (ha:0<a) (hq:2≤q)
    {v:Finset (Fin m)→ℝ}{L H:ℝ}{hLH:L≤H}
    (Φ:RecordingFunction a q m v L H hLH)
    (x:Q p) (parent:Space (a*p) q m) (t:Set.Icc L H)
    (hZero:actualChildT hp ha hq Φ ((x,parent),t)=0):
    Nonempty (ChildLotteryBank parent v t.val):=by
  apply exists_childLotteryBank hp ha Φ parent
    ((auxiliaryGraphFamily hp ha hq).map (x,parent)) t
    ((auxiliaryGraphFamily hp ha hq).within x parent)
  intro i
  exact congrFun hZero i

end FairDivision.BF.Recording
