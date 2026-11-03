import FairDivision.Topology.AAK.SuspendedJoinPrismSelection

/-!
# From a zero-free cyclic reversal to the actual finite relative prism data

This composes the explicit normalization, endpoint cones, barycentric target
classifier, and the imported DKGM fine source chains. The conclusion contains
actual vertex maps on a common finite time grid, not a homotopy-invariance
hypothesis. The next chain assembly applies the concrete relative target
boundary and the imported Dold exactness to these data.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.AAK.SuspendedJoinPrismSelection

open Dvoretzky Dvoretzky.Dold ZeroFreeBipyramid
open FairDivision.Topology
open scoped Classical

variable (p : ℕ) [Fact p.Prime]

/-- The actual target homotopy forced by a hypothetical zero-free reversal. -/
def fromZeroFree (H : C(Source p × unitInterval, ZMod p → ℝ))
    (hn : ∀q,H q≠0)
    (hneg : ∀x v,H (x,0) v<0) (hpos : ∀x v,0<H (x,1) v) :
    C(unitInterval × Source p, Target p) :=
  (suspendedPoleHomotopy p H hn hneg hpos).toContinuousMap

@[simp] theorem fromZeroFree_south
    (H : C(Source p × unitInterval, ZMod p → ℝ)) (hn : ∀q,H q≠0)
    (hneg : ∀x v,H (x,0) v<0) (hpos : ∀x v,0<H (x,1) v) (x : Source p) :
    fromZeroFree p H hn hneg hpos (0,x)=suspensionPole (p-1) (ZMod p) false :=
  (suspendedPoleHomotopy p H hn hneg hpos).map_zero_left x

@[simp] theorem fromZeroFree_north
    (H : C(Source p × unitInterval, ZMod p → ℝ)) (hn : ∀q,H q≠0)
    (hneg : ∀x v,H (x,0) v<0) (hpos : ∀x v,0<H (x,1) v) (x : Source p) :
    fromZeroFree p H hn hneg hpos (1,x)=suspensionPole (p-1) (ZMod p) true :=
  (suspendedPoleHomotopy p H hn hneg hpos).map_one_left x

/-- The sign convention matches the imported DKGM action, which translates
vertex labels by multiplication with g⁻¹. -/
theorem fromZeroFree_equivariant
    (H : C(Source p × unitInterval, ZMod p → ℝ)) (hn : ∀q,H q≠0)
    (hneg : ∀x v,H (x,0) v<0) (hpos : ∀x v,0<H (x,1) v)
    (heq : ∀g x t,H (sourceAct p g x,t)=
      permuteVector (cyclicPerm (-g.toAdd)) (H (x,t))) :
    ∀g t x,fromZeroFree p H hn hneg hpos (t,sourceAct p g x)=
      suspensionRelabel p (-g.toAdd) (fromZeroFree p H hn hneg hpos (t,x)) := by
  let action : ZMod p→Source p→Source p :=
    fun a=>sourceAct p (Multiplicative.ofAdd (-a))
  have heq' : ∀a x t,H (action a x,t)=permuteVector (cyclicPerm a) (H (x,t)) := by
    intro a x t
    simpa [action] using heq (Multiplicative.ofAdd (-a)) x t
  intro g t x
  simpa [action,fromZeroFree] using
    suspendedPoleHomotopy_equivariant p action H hn hneg hpos heq' (-g.toAdd) t x

/-- The entire geometric input to the relative chain contradiction is
constructed from the literal hypothetical zero-free continuous map. -/
theorem zero_free_prism_data
    (H : C(Source p × unitInterval, ZMod p → ℝ)) (hn : ∀q,H q≠0)
    (hneg : ∀x v,H (x,0) v<0) (hpos : ∀x v,0<H (x,1) v)
    (heq : ∀g x t,H (sourceAct p g x,t)=
      permuteVector (cyclicPerm (-g.toAdd)) (H (x,t))) :
    ∃ (K : ℕ) (hK : 0<K) (r : ℕ)
      (sel : Fin (K+1)→SourceSpace p→TargetVertex p),
      (∀x∈GroupJoin (Multiplicative (ZMod p)) p,sel 0 x=pole false) ∧
      (∀x∈GroupJoin (Multiplicative (ZMod p)) p,sel (Fin.last K) x=pole true) ∧
      (∀j g x,x∈GroupJoin (Multiplicative (ZMod p)) p→
        sel j (joinAct g x)=suspensionTranslate (-g.toAdd) (sel j x)) ∧
      (∀k≤p-1,∀l∈(fineChain p r k).support,
        l.length=k+1 ∧ (∀x∈l,x∈GroupJoin (Multiplicative (ZMod p)) p) ∧
        ∀j : Fin K,PrismFace p (sel j.castSucc) (sel j.succ) l) :=
  exists_fine_prism_selection p (fromZeroFree p H hn hneg hpos)
    (fromZeroFree_south p H hn hneg hpos)
    (fromZeroFree_north p H hn hneg hpos)
    (fromZeroFree_equivariant p H hn hneg hpos heq)

end FairDivision.Topology.AAK.SuspendedJoinPrismSelection
