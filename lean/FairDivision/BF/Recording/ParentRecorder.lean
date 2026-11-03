import FairDivision.BF.Recording.ChildLotteryBank
import FairDivision.Topology.Recording.ProjectedZeros

/-!
# Project and record the SAME actual simultaneous child zeros

This is the manuscript's signed-distance parent construction. The actual
fixed-Qp family and actual T are already proved. Only the separate AAK
pathwise-zero statement is supplied here. Every zero retains its actual
common-inventory bank of equitable child lotteries, ready for their product.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

open scoped unitInterval Topology

namespace FairDivision.BF.Recording

open FairDivision.Topology FairDivision.Topology.NerveConnectivity

abbrev ParentParameters (p a q m:ℕ) (L H:ℝ):=
  Space (a*p) q m×Set.Icc L H

/-- Associativity transport only; this is EXACTLY actualChildT. -/
def parentChildT {p a q m:ℕ} (hp:2≤p) (ha:0<a) (hq:2≤q)
    {v:Finset (Fin m)→ℝ}{L H:ℝ}{hLH:L≤H}
    (Φ:RecordingFunction a q m v L H hLH):
    C(Q p×ParentParameters p a q m L H,Fin p→ℝ):=
  (actualChildT hp ha hq Φ).comp
    ((Homeomorph.prodAssoc (Q p) (Space (a*p) q m) (Set.Icc L H)).symm :
      C(Q p×ParentParameters p a q m L H,(Q p×Space (a*p) q m)×Set.Icc L H))

def lowerBoundary {p a q m:ℕ}{L H:ℝ} (hLH:L≤H):
    Set (ParentParameters p a q m L H):={z|z.2=lowerTarget hLH}

def upperBoundary {p a q m:ℕ}{L H:ℝ} (hLH:L≤H):
    Set (ParentParameters p a q m L H):={z|z.2=upperTarget hLH}

/-- The exact external AAK output required along actual paths in the
parent graph-times-interval space. It concerns the constructed T only. -/
def HasRecordingPathwiseZeros {p a q m:ℕ} (hp:2≤p) (ha:0<a) (hq:2≤q)
    {v:Finset (Fin m)→ℝ}{L H:ℝ}{hLH:L≤H}
    (Φ:RecordingFunction a q m v L H hLH):Prop:=
  FairDivision.Topology.Recording.HasPathwiseZeros (parentChildT hp ha hq Φ)
    (lowerBoundary hLH) (upperBoundary hLH)

/-- One actual vertical path over a fixed graph point, used for nonemptiness
of the projected zero set. -/
def verticalParameterPath {p a q m:ℕ}{L H:ℝ} (hLH:L≤H)
    (b:Space (a*p) q m):
    Path (b,lowerTarget hLH) (b,upperTarget hLH) where
  toFun s:=(b,⟨(1-s.val)*L+s.val*H,
    by
      have hProduct:0 ≤ s.val*(H-L):=mul_nonneg s.2.1 (sub_nonneg.mpr hLH)
      nlinarith only [hProduct],
    by
      have hProduct:0≤(1-s.val)*(H-L):=
        mul_nonneg (sub_nonneg.mpr s.2.2) (sub_nonneg.mpr hLH)
      nlinarith only [hProduct]⟩)
  continuous_toFun:=continuous_const.prodMk
    ((((continuous_const.sub continuous_subtype_val).mul continuous_const).add
      (continuous_subtype_val.mul continuous_const)).subtype_mk _)
  source':=by
    apply Prod.ext
    ·rfl
    ·apply Subtype.ext
     change (1-(0:ℝ))*L+(0:ℝ)*H=L
     simp only [sub_zero,one_mul,zero_mul,add_zero]
  target':=by
    apply Prod.ext
    ·rfl
    ·apply Subtype.ext
     change (1-(1:ℝ))*L+(1:ℝ)*H=H
     simp only [sub_self,zero_mul,one_mul,zero_add]

/-- The manuscript's actual signed-distance recorder, retaining each bank
at its exact simultaneous zero. Nonempty graph is the branch used here;
the empty graph branch of the final recorder is vacuous. -/
theorem exists_parent_bankRecorder {p a q m:ℕ}
    (hp:2≤p) (ha:0<a) (hq:2≤q)
    {v:Finset (Fin m)→ℝ}{L H:ℝ}{hLH:L≤H}
    (Φ:RecordingFunction a q m v L H hLH)
    (hPath:HasRecordingPathwiseZeros hp ha hq Φ)
    (hGraph:Nonempty (Space (a*p) q m)):
    ∃Ψ:C(ParentParameters p a q m L H,ℝ),
      (∀b,Ψ (b,lowerTarget hLH)<0) ∧
      (∀b,0<Ψ (b,upperTarget hLH)) ∧
      (∀b t,Ψ (b,t)=0→Nonempty (ChildLotteryBank b v t.val)) ∧
      ∀z,Ψ z=0↔∃x:Q p,parentChildT hp ha hq Φ (x,z)=0:=by
  classical
  letI : CompactSpace (Q p):=isCompact_iff_compactSpace.mp
    (simplicialRealization_isCompact (Volovikov.universalJoinComplex p (ChildGroup p)))
  letI : LocallyPathConnectedSpace (Set.Icc L H):=
    convex_locallyPathConnectedSpace (convex_Icc L H)
  let b₀:Space (a*p) q m:=Classical.choice hGraph
  have hLower:∀(x:Q p)(z:ParentParameters p a q m L H),z∈lowerBoundary hLH→
      ∀i,parentChildT hp ha hq Φ (x,z) i<0:=by
    intro x z hz i
    change z.2=lowerTarget hLH at hz
    change actualChildT hp ha hq Φ ((x,z.1),z.2) i<0
    rw [hz]
    exact actualChildT_lower hp ha hq Φ x z.1 i
  have hUpper:∀(x:Q p)(z:ParentParameters p a q m L H),z∈upperBoundary hLH→
      ∀i,0<parentChildT hp ha hq Φ (x,z) i:=by
    intro x z hz i
    change z.2=upperTarget hLH at hz
    change 0<actualChildT hp ha hq Φ ((x,z.1),z.2) i
    rw [hz]
    exact actualChildT_upper hp ha hq Φ x z.1 i
  obtain ⟨Ψ,hNeg,hPos,hZero⟩:=FairDivision.Topology.Recording.exists_projectedZero_recorder
    (by omega:0<p) (parentChildT hp ha hq Φ) (lowerBoundary hLH) (upperBoundary hLH)
    hLower hUpper hPath (a:=(b₀,lowerTarget hLH)) (b:=(b₀,upperTarget hLH))
    rfl rfl (verticalParameterPath hLH b₀)
  refine ⟨Ψ,fun b=>hNeg _ rfl,fun b=>hPos _ rfl,?_,hZero⟩
  intro b t hΨ
  obtain ⟨x,hx⟩:=(hZero (b,t)).mp hΨ
  exact actualChildT_zero_childLotteryBank hp ha hq Φ x b t hx

end FairDivision.BF.Recording
