import FairDivision.BF.Recording.ParentRecorder
import FairDivision.Topology.Recording.CompatibleLotteryProduct

/-!
# The manuscript's prime-multiplication step

At every actual simultaneous child zero, take the literal independent
product of the actual disjoint-stock child lotteries. Project those zeros
and use the manuscript signed-distance recorder. The only external premise
in this intermediate composition is the exact AAK pathwise-zero statement
for the already constructed continuous T. It is discharged by AAKPathwise.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace FairDivision.BF.Recording

open FairDivision.Topology

/-- Independent product of the actual bank certifies the parent zero. -/
theorem ChildLotteryBank.certifies {p a q m:ℕ} {parent:Space (a*p) q m}
    {v:Finset (Fin m)→ℝ}{t:ℝ} (bank:ChildLotteryBank parent v t):
    Certifies v parent t:=by
  obtain ⟨μ,hCompatible,hPool,hMean⟩:=
    FairDivision.Topology.Recording.exists_equitable_product_lottery
      bank.lottery bank.compatible bank.stock bank.in_stock bank.stock_disjoint
      (fun B=>v (realPart B)) t bank.equitable
  refine ⟨μ,hCompatible,?_,hMean⟩
  intro j z hz
  obtain ⟨i,hi,hzi⟩:=Finset.mem_biUnion.mp (hPool j hz)
  exact bank.stock_available i hzi

/-- Every zero of the actual constructed T is an actual parent lottery,
with no child-zero, relabeling, or product premise remaining. -/
theorem actualChildT_zero_certifies {p a q m:ℕ}
    (hp:2≤p) (ha:0<a) (hq:2≤q)
    {v:Finset (Fin m)→ℝ}{L H:ℝ}{hLH:L≤H}
    (Φ:RecordingFunction a q m v L H hLH)
    (x:Q p) (parent:Space (a*p) q m) (t:Set.Icc L H)
    (hZero:actualChildT hp ha hq Φ ((x,parent),t)=0):
    Certifies v parent t.val:=by
  obtain ⟨bank⟩:=actualChildT_zero_childLotteryBank hp ha hq Φ x parent t hZero
  exact bank.certifies

/-- The same manuscript multiplication proof, with its separately proved
AAK pathwise theorem isolated at exactly its point of use. -/
theorem primeMultiplication_of_pathwiseZeros {p a q m:ℕ}
    (hp:2≤p) (ha:0<a) (hq:2≤q)
    {v:Finset (Fin m)→ℝ}{L H:ℝ}{hLH:L≤H}
    (Φ:RecordingFunction a q m v L H hLH)
    (hPath:HasRecordingPathwiseZeros hp ha hq Φ):
    Nonempty (RecordingFunction (a*p) q m v L H hLH):=by
  classical
  by_cases hGraph:Nonempty (Space (a*p) q m)
  ·obtain ⟨Ψ,hNegative,hPositive,hZeroBank,hZeroSet⟩:=
      exists_parent_bankRecorder hp ha hq Φ hPath hGraph
   exact ⟨{
     phi:=Ψ
     negative:=hNegative
     positive:=hPositive
     realizes:=by
       intro b t hZero
       obtain ⟨bank⟩:=hZeroBank b t hZero
       exact bank.certifies }⟩
  ·letI : IsEmpty (Space (a*p) q m):=⟨fun b=>hGraph ⟨b⟩⟩
   exact ⟨{
     phi:=ContinuousMap.const _ 0
     negative:=fun b=>isEmptyElim b
     positive:=fun b=>isEmptyElim b
     realizes:=fun b=>isEmptyElim b }⟩

end FairDivision.BF.Recording
