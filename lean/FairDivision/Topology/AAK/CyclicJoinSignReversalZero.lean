import FairDivision.Topology.AAK.RelativePrismObstruction
import FairDivision.Topology.Volovikov.UniversalJoinDKGMRealization

/-!
# The continuous cyclic zero theorem on the existing universal-join realization

Reuse the existing exact local/DKGM homeomorphism, including its inverse
translation convention. The final statement is on the repository's original
probability-simplex realization and its original additive translation. It has
no approximation, genericity, local-degree, exactness, or invariance premise.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.AAK

open FairDivision.Topology.NerveConnectivity FairDivision.Topology.Volovikov
open ZeroFreeBipyramid
open scoped Classical

/-- The exact p-fold source already used by the BF topological bridge. -/
abbrev CyclicZeroSource (p : ℕ) [NeZero p] := simplicialRealization (universalJoinComplex p (ZMod p))

/-- Every continuous cyclic-equivariant p-coordinate homotopy with strict
opposite signs at its endpoints has a zero on the p-fold cyclic join. -/
theorem cyclicJoin_signReversalZero (p : ℕ) [Fact p.Prime]
    (H : C(CyclicZeroSource p × unitInterval, ZMod p→ℝ))
    (heq : ∀a x t,H (translateJoinRealization a x,t)=
      permuteVector (cyclicPerm a) (H (x,t)))
    (hneg : ∀x v,H (x,0) v<0) (hpos : ∀x v,0<H (x,1) v) :
    ∃ (t : unitInterval) (x : CyclicZeroSource p), H (x,t)=0 := by
  let e:=universalJoinDKGMHomeomorph p (ZMod p)
  let Hd : C(SuspendedJoinPrismSelection.Source p × unitInterval, ZMod p→ℝ):=
    H.comp ⟨fun q=>(e.symm q.1,q.2),
      (e.symm.continuous.comp continuous_fst).prodMk continuous_snd⟩
  have hdEq : ∀g x t,Hd (SuspendedJoinPrismSelection.sourceAct p g x,t)=
      permuteVector (cyclicPerm (-g.toAdd)) (Hd (x,t)) := by
    intro g x t
    change H (e.symm (SuspendedJoinPrismSelection.sourceAct p g x),t)=_
    have hAct : e.symm (SuspendedJoinPrismSelection.sourceAct p g x)=
        translateJoinRealization (-g.toAdd) (e.symm x) := by
      exact universalJoinDKGMHomeomorph_symm_translate g.toAdd x
    rw [hAct]
    exact heq (-g.toAdd) (e.symm x) t
  obtain ⟨q,hq⟩:=RelativePrismObstruction.cyclic_sign_reversal_has_zero p Hd
    (fun x v=>hneg (e.symm x) v) (fun x v=>hpos (e.symm x) v) hdEq
  exact ⟨q.2,e.symm q.1,hq⟩

/-- Restricting a rectangle map along an arbitrary continuous left-to-right
path gives the exact pathwise zero conclusion used by BF. The auxiliary
parameter space need not itself be an interval. -/
theorem cyclicJoin_pathwiseSeparation (p : ℕ) [Fact p.Prime]
    {J : Type*} [TopologicalSpace J]
    (F : C(CyclicZeroSource p × unitInterval × J, ZMod p→ℝ))
    (heq : ∀a x t j,F (translateJoinRealization a x,t,j)=
      permuteVector (cyclicPerm a) (F (x,t,j)))
    (hneg : ∀x j v,F (x,0,j) v<0) (hpos : ∀x j v,0<F (x,1,j) v)
    (γ : C(unitInterval,unitInterval×J)) (hγ0 : (γ 0).1=0) (hγ1 : (γ 1).1=1) :
    ∃ (s : unitInterval) (x : CyclicZeroSource p), F (x,(γ s).1,(γ s).2)=0 := by
  let H : C(CyclicZeroSource p × unitInterval,ZMod p→ℝ):=
    F.comp ⟨fun q=>(q.1,γ q.2),continuous_fst.prodMk (γ.continuous.comp continuous_snd)⟩
  exact cyclicJoin_signReversalZero p H
    (fun a x t=>heq a x (γ t).1 (γ t).2)
    (fun x v=>by
      change F (x,(γ 0).1,(γ 0).2) v<0
      rw [hγ0]
      exact hneg x (γ 0).2 v)
    (fun x v=>by
      change 0<F (x,(γ 1).1,(γ 1).2) v
      rw [hγ1]
      exact hpos x (γ 1).2 v)

end FairDivision.Topology.AAK
