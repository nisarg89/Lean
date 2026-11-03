import FairDivision.BF.Recording.ParentRecorder
import FairDivision.Topology.AAK.CyclicJoinSignReversalZero
import FairDivision.Topology.Volovikov.PositionAction

/-!
# The actual AAK pathwise input for the manuscript's fixed symmetric source

The recording construction uses the SAME p-fold join of S_p at every graph
point. Embed the p-fold cyclic join into it by the regular position
permutations. Restrict the actual score map along the actual parent path and
reindex its p coordinates. The unconditional cyclic sign-reversal theorem
then gives a simultaneous zero in this SAME fixed symmetric source.

No AAK statement, family map, or pathwise-zero oracle remains in the public
recording theorem below. The external obstruction proof is allowed to use the
imported Dold/prism route; the manuscript's parent graph and recorder are
unchanged.
-/

set_option autoImplicit false

noncomputable section

open scoped unitInterval Topology Classical

namespace FairDivision.BF.Recording

open FairDivision.Topology FairDivision.Topology.NerveConnectivity
open FairDivision.Topology.Volovikov
open FairDivision.Topology.AAK

variable {p : ℕ}

/-- The regular cyclic subgroup, in the manuscript's additive S_p wrapper. -/
def cyclicChildLabel (e : Fin p≃ZMod p) (a : ZMod p) : ChildGroup p :=
  Additive.ofMul (regularPositionPerm e a)

@[simp] theorem cyclicChildLabel_zero (e : Fin p≃ZMod p) : cyclicChildLabel e 0=0 := by
  change Additive.ofMul (regularPositionPerm e 0)=0
  rw [regularPositionPerm_zero]
  rfl

theorem cyclicChildLabel_add (e : Fin p≃ZMod p) (a b : ZMod p) :
    cyclicChildLabel e (a+b)=cyclicChildLabel e a+cyclicChildLabel e b := by
  exact congrArg Additive.ofMul (regularPositionPerm_add e a b)

def cyclicChildVertex (e : Fin p≃ZMod p) (v : Fin p×ZMod p) : Fin p×ChildGroup p :=
  (v.1,cyclicChildLabel e v.2)

/-- The color-preserving cyclic subgroup map carries actual join faces to
actual symmetric-source faces. -/
theorem cyclicChildVertex_face (e : Fin p≃ZMod p)
    {S : Finset (Fin p×ZMod p)} (hS : S∈universalJoinComplex p (ZMod p)) :
    S.image (cyclicChildVertex e)∈universalJoinComplex p (ChildGroup p) := by
  refine ⟨hS.1.image _,?_⟩
  intro i g h hg hh
  obtain ⟨v,hv,hvg⟩:=Finset.mem_image.mp hg
  obtain ⟨w,hw,hwh⟩:=Finset.mem_image.mp hh
  have hvi : v.1=i:=congrArg Prod.fst hvg
  have hwi : w.1=i:=congrArg Prod.fst hwh
  have hvw : v.2=w.2:=hS.2 i v.2 w.2
    (by simpa only [←hvi,Prod.mk.eta] using hv)
    (by simpa only [←hwi,Prod.mk.eta] using hw)
  have hg' : cyclicChildLabel e v.2=g:=congrArg Prod.snd hvg
  have hh' : cyclicChildLabel e w.2=h:=congrArg Prod.snd hwh
  exact hg'.symm.trans ((congrArg (cyclicChildLabel e) hvw).trans hh')

/-- Actual continuous inclusion into the fixed Q_p of the recording proof. -/
def cyclicChildInclude [NeZero p] (e : Fin p≃ZMod p) : C(CyclicZeroSource p,Q p) where
  toFun x:=⟨stdSimplex.map (cyclicChildVertex e) x.1,
    ((universalJoinComplex p (ChildGroup p)).isRelLowerSet_faces
      (cyclicChildVertex_face e x.2)).2
      (FairDivision.Topology.finiteSimplexSupport_map_subset _ _)
      (finiteSimplexSupport_nonempty _)⟩
  continuous_toFun:=((stdSimplex.continuous_map _).comp continuous_subtype_val).subtype_mk _

/-- Its exact symmetry is the SAME qAction used by all child graph maps. -/
theorem cyclicChildInclude_equivariant [NeZero p] (e : Fin p≃ZMod p) (a : ZMod p)
    (x : CyclicZeroSource p) :
    cyclicChildInclude e (translateJoinRealization a x)=
      qAction (cyclicChildLabel e a) (cyclicChildInclude e x) := by
  apply Subtype.ext
  change stdSimplex.map (cyclicChildVertex e)
      (stdSimplex.map (translateJoinVertex a) x.1)=
    stdSimplex.map (translateJoinVertex (cyclicChildLabel e a))
      (stdSimplex.map (cyclicChildVertex e) x.1)
  rw [stdSimplex.map_comp_apply,stdSimplex.map_comp_apply]
  congr 1
  funext v
  rcases v with ⟨i,g⟩
  exact Prod.ext rfl (cyclicChildLabel_add e a g)

/-- Unconditional pathwise zeros for any equivariant continuous p-score map
on the SAME symmetric source. Both endpoint sets and paths are literal. -/
theorem symmetricJoin_hasPathwiseZeros [Fact p.Prime]
    {Y : Type*} [TopologicalSpace Y]
    (T : C(Q p×Y,Fin p→ℝ)) (lower upper : Set Y)
    (heq : ∀g x y i,T (qAction g x,y) (g.toMul i)=T (x,y) i)
    (hLower : ∀x y,y∈lower→∀i,T (x,y) i<0)
    (hUpper : ∀x y,y∈upper→∀i,0<T (x,y) i) :
    FairDivision.Topology.Recording.HasPathwiseZeros T lower upper := by
  classical
  let e : Fin p≃ZMod p:=(Fintype.equivFinOfCardEq (ZMod.card p)).symm
  intro a ha b hb γ
  let H : C(CyclicZeroSource p×unitInterval,ZMod p→ℝ):=
    ⟨fun z g=>T (cyclicChildInclude e z.1,γ z.2) (e.symm g),by
      apply continuous_pi
      intro g
      exact (continuous_apply (e.symm g)).comp
        (T.continuous.comp (((cyclicChildInclude e).continuous.comp continuous_fst).prodMk
          (γ.continuous.comp continuous_snd)))⟩
  have hEq : ∀r x t,H (translateJoinRealization r x,t)=
      AAK.ZeroFreeBipyramid.permuteVector (AAK.ZeroFreeBipyramid.cyclicPerm r) (H (x,t)) := by
    intro r x t
    funext g
    change T (cyclicChildInclude e (translateJoinRealization r x),γ t) (e.symm g)=_
    rw [cyclicChildInclude_equivariant]
    have hi : (cyclicChildLabel e r).toMul (e.symm (-r+g))=e.symm g := by
      simp [cyclicChildLabel,regularPositionPerm_apply,add_assoc]
    have h:=heq (cyclicChildLabel e r) (cyclicChildInclude e x) (γ t) (e.symm (-r+g))
    rw [hi] at h
    simpa [H,AAK.ZeroFreeBipyramid.permuteVector,AAK.ZeroFreeBipyramid.cyclicPerm] using h
  obtain ⟨t,x,hZero⟩:=cyclicJoin_signReversalZero p H hEq
    (fun x g=>by simpa [H] using hLower (cyclicChildInclude e x) a ha (e.symm g))
    (fun x g=>by simpa [H] using hUpper (cyclicChildInclude e x) b hb (e.symm g))
  refine ⟨t,cyclicChildInclude e x,?_⟩
  funext i
  have hi:=congrFun hZero (e i)
  simpa [H] using hi

/-- The exact pathwise hypothesis of the actual manuscript parent recorder
is now proved for the fully constructed child score map. -/
theorem recording_pathwiseZeros [Fact p.Prime]
    {a q m : ℕ} (hp : 2≤p) (ha : 0<a) (hq : 2≤q)
    {v : Finset (Fin m)→ℝ} {L H : ℝ} {hLH : L≤H}
    (Φ : RecordingFunction a q m v L H hLH) :
    HasRecordingPathwiseZeros hp ha hq Φ := by
  apply symmetricJoin_hasPathwiseZeros (parentChildT hp ha hq Φ)
    (lowerBoundary hLH) (upperBoundary hLH)
  · intro g x y i
    exact actualChildT_equivariant hp ha hq Φ g x y.1 y.2 i
  · intro x y hy i
    change y.2=lowerTarget hLH at hy
    change actualChildT hp ha hq Φ ((x,y.1),y.2) i<0
    rw [hy]
    exact actualChildT_lower hp ha hq Φ x y.1 i
  · intro x y hy i
    change y.2=upperTarget hLH at hy
    change 0<actualChildT hp ha hq Φ ((x,y.1),y.2) i
    rw [hy]
    exact actualChildT_upper hp ha hq Φ x y.1 i

/-- Prime-indexed facade used by the manuscript's exact prime-factor
recursion. The numerical lower bound is supplied by the prime itself. -/
theorem hasRecordingPathwiseZeros (p a q m : ℕ) [Fact p.Prime]
    (ha : 0<a) (hq : 2≤q)
    {v : Finset (Fin m)→ℝ} {L H : ℝ} {hLH : L≤H}
    (Φ : RecordingFunction a q m v L H hLH) :
    HasRecordingPathwiseZeros (Fact.out : p.Prime).two_le ha hq Φ :=
  recording_pathwiseZeros (Fact.out : p.Prime).two_le ha hq Φ

/-- Public actual parent recorder, with the external AAK pathwise premise
discharged and every zero retaining its SAME child-lottery bank. -/
theorem exists_parent_bankRecorder_unconditional [Fact p.Prime]
    {a q m : ℕ} (hp : 2≤p) (ha : 0<a) (hq : 2≤q)
    {v : Finset (Fin m)→ℝ} {L H : ℝ} {hLH : L≤H}
    (Φ : RecordingFunction a q m v L H hLH) (hGraph : Nonempty (Space (a*p) q m)) :
    ∃Ψ : C(ParentParameters p a q m L H,ℝ),
      (∀b,Ψ (b,lowerTarget hLH)<0) ∧
      (∀b,0<Ψ (b,upperTarget hLH)) ∧
      (∀b t,Ψ (b,t)=0→Nonempty (ChildLotteryBank b v t.val)) ∧
      ∀z,Ψ z=0↔∃x : Q p,parentChildT hp ha hq Φ (x,z)=0 :=
  exists_parent_bankRecorder hp ha hq Φ (recording_pathwiseZeros hp ha hq Φ) hGraph

end FairDivision.BF.Recording
