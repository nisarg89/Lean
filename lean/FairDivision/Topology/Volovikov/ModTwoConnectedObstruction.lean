import FairDivision.Topology.Volovikov.ModTwoJoinObstruction
import FairDivision.Topology.Volovikov.UniversalJoinEquivariantTransfer
import FairDivision.Topology.Volovikov.AssociatedOrbitSection
import FairDivision.Topology.Volovikov.ReducedSphereJoinReduction
import FairDivision.Topology.Volovikov.ZeroReduction

/-!
# The unconditional elementary-abelian two-group connected-source obstruction

The existing equivariant cellular transfer maps the finite universal join
into any sufficiently null-connected source. Composing a hypothetical
nowhere-zero centered map with that SAME transfer contradicts the imported
chain-level obstruction through ModTwoJoinObstruction.

The reduced-sphere and score statements below contain no no-map, Euler,
index, or character-class hypothesis. They use the concrete position
permutation action already used by the BF score reductions. This is the
p=2 external topological theorem, not the odd-prime Volovikov theorem.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology FairDivision.Topology.NerveConnectivity

/-- No centered, zero-free equivariant map out of a sufficiently connected
source carrying a continuous action of the elementary abelian two-group. -/
theorem no_centered_real_connectedMap_modTwo {r k : ℕ} {X : Type*}
    [TopologicalSpace X] (hr : 0<r) (hDimension : 2^r≤k+2)
    (hX : NullConnectedSpace k X)
    (sourceAction : (Fin r → ZMod 2) → X ≃ₜ X)
    (hSourceAction : IsContinuousAddAction sourceAction)
    (f : C(X,(Fin r → ZMod 2) → ℝ))
    (hCenter : ∀ x,∑ g : Fin r → ZMod 2,f x g=0)
    (hNonzero : ∀ x,f x≠0)
    (hEquiv : ∀ a x g,f (sourceAction a x) g=f x (g-a)) : False := by
  obtain ⟨transfer,hTransfer⟩:=exists_equivariant_universalJoinMap
    (m:=2^r) hDimension hX sourceAction hSourceAction
  apply no_centered_real_joinMap_modTwo hr le_rfl (f.comp transfer)
  · intro x
    exact hCenter (transfer x)
  · intro x
    exact hNonzero (transfer x)
  · intro a x g
    have hTranslate:transfer (translateJoinRealization a x)=sourceAction a (transfer x):=by
      simpa only [translateInvariant_universal_eq_join] using hTransfer a x
    change f (transfer (translateJoinRealization a x)) g=f (transfer x) (g-a)
    rw [hTranslate]
    exact hEquiv a (transfer x) g

/-- Zero form of the same unconditional connected-source theorem. -/
theorem exists_centered_real_zero_modTwo {r k : ℕ} {X : Type*}
    [TopologicalSpace X] (hr : 0<r) (hDimension : 2^r≤k+2)
    (hX : NullConnectedSpace k X)
    (sourceAction : (Fin r → ZMod 2) → X ≃ₜ X)
    (hSourceAction : IsContinuousAddAction sourceAction)
    (f : X → (Fin r → ZMod 2) → ℝ) (hContinuous : Continuous f)
    (hCenter : ∀ x,∑ g : Fin r → ZMod 2,f x g=0)
    (hEquiv : ∀ a x g,f (sourceAction a x) g=f x (g-a)) :
    ∃ x,f x=0 := by
  by_contra hNoZero
  apply no_centered_real_connectedMap_modTwo hr hDimension hX sourceAction hSourceAction
    ⟨f,hContinuous⟩ hCenter
  · intro x hx
    exact hNoZero ⟨x,hx⟩
  · exact hEquiv

/-- Actual no-map theorem into the concrete reduced regular sphere with
its existing pTorusPositionPerm action, specialized to p=2. -/
theorem no_reducedSphere_map_modTwo {r k : ℕ} {X : Type*}
    [TopologicalSpace X] (hr : 0<r) (hDimension : 2^r≤k+2)
    (hX : NullConnectedSpace k X)
    (sourceAction : (Fin r → ZMod 2) → X ≃ₜ X)
    (hSourceAction : IsContinuousAddAction sourceAction)
    (F : X → ReducedSphere (2^r)) (hContinuous : Continuous F)
    (hEquiv : ∀ a x,F (sourceAction a x)=
      relabelReducedSphere (pTorusPositionPerm 2 r a) (F x)) : False := by
  let e:=pTorusPositionEquiv 2 r
  let f : C(X,(Fin r → ZMod 2) → ℝ):=
    ⟨fun x g=>(F x).1 (e.symm g),by
      apply continuous_pi
      intro g
      exact (continuous_apply (e.symm g)).comp
        (continuous_subtype_val.comp hContinuous)⟩
  have hCenter:∀x,∑ g : Fin r → ZMod 2,f x g=0:=by
    intro x
    exact (e.symm.sum_comp (F x).1).trans (F x).2.1
  have hNonzero:∀x,f x≠0:=by
    intro x hx
    have hZero:(F x).1=0:=by
      funext i
      have hi:=congrFun hx (e i)
      change (F x).1 (e.symm (e i))=0 at hi
      simpa only [Equiv.symm_apply_apply,Pi.zero_apply] using hi
    have hNorm:(∑i:Fin (2^r),((F x).1 i)^2)=0:=by
      simp only [hZero,Pi.zero_apply,pow_two,zero_mul,Finset.sum_const_zero]
    exact one_ne_zero ((F x).2.2.symm.trans hNorm)
  apply no_centered_real_connectedMap_modTwo hr hDimension hX sourceAction hSourceAction
    f hCenter hNonzero
  intro a x g
  change (F (sourceAction a x)).1 (e.symm g)=(F x).1 (e.symm (g-a))
  rw [hEquiv a x]
  exact congrArg (F x).1 (regularPositionPerm_symm_index e a g)

/-- The concrete centered position-score map has a zero. Reuses the prior
normalization reduction verbatim; its former topological premise is now
proved by the mod-two theorem above. -/
theorem exists_centered_position_zero_modTwo {r k : ℕ} {X : Type*}
    [TopologicalSpace X] (hr : 0<r) (hDimension : 2^r≤k+2)
    (hX : NullConnectedSpace k X)
    (sourceAction : (Fin r → ZMod 2) → X ≃ₜ X)
    (hSourceAction : IsContinuousAddAction sourceAction)
    (score : X → Fin (2^r) → ℝ) (hContinuous : Continuous score)
    (hCenter : ∀x,∑i:Fin (2^r),score x i=0)
    (hEquiv : ∀ a x i,score (sourceAction a x) (pTorusPositionPerm 2 r a i)=score x i) :
    ∃ x,score x=0 := by
  apply zero_of_reducedSphere_obstruction (fun a x=>sourceAction a x)
    (pTorusPositionPerm 2 r) score hContinuous hCenter hEquiv
  intro F hF hEq
  exact no_reducedSphere_map_modTwo hr hDimension hX sourceAction hSourceAction F hF hEq

/-- Equalization form: centering any continuous regularly equivariant
position-score vector produces a zero, so all original coordinates agree. -/
theorem exists_equal_position_scores_modTwo {r k : ℕ} {X : Type*}
    [TopologicalSpace X] (hr : 0<r) (hDimension : 2^r≤k+2)
    (hX : NullConnectedSpace k X)
    (sourceAction : (Fin r → ZMod 2) → X ≃ₜ X)
    (hSourceAction : IsContinuousAddAction sourceAction)
    (score : X → Fin (2^r) → ℝ) (hContinuous : Continuous score)
    (hEquiv : ∀ a x i,score (sourceAction a x) (pTorusPositionPerm 2 r a i)=score x i) :
    ∃ x,∀ i j,score x i=score x j := by
  let average:X→ℝ:=fun x=>(∑i:Fin (2^r),score x i)/(2^r:ℕ)
  let centered:X→Fin (2^r)→ℝ:=fun x i=>score x i-average x
  have hn:((2^r:ℕ):ℝ)≠0:=by positivity
  have hAverage:Continuous average:=by
    exact (continuous_finset_sum _ (fun i hi=>(continuous_apply i).comp hContinuous)).div_const _
  have hCentered:Continuous centered:=by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp hContinuous).sub hAverage
  have hSum:∀x,∑i:Fin (2^r),centered x i=0:=by
    intro x
    simp only [centered,average,Finset.sum_sub_distrib,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp [hn] <;> ring
  have hAverageEquiv:∀a x,average (sourceAction a x)=average x:=by
    intro a x
    unfold average
    congr 1
    calc
      (∑i:Fin (2^r),score (sourceAction a x) i)=
          ∑i:Fin (2^r),score (sourceAction a x) (pTorusPositionPerm 2 r a i):=
        (Equiv.sum_comp (pTorusPositionPerm 2 r a)
          (fun i : Fin (2^r) => score (sourceAction a x) i)).symm
      _=∑i:Fin (2^r),score x i:=Finset.sum_congr rfl (fun i hi=>hEquiv a x i)
  have hCenteredEquiv:∀a x i,
      centered (sourceAction a x) (pTorusPositionPerm 2 r a i)=centered x i:=by
    intro a x i
    simp only [centered,hEquiv,hAverageEquiv]
  obtain ⟨x,hx⟩:=exists_centered_position_zero_modTwo hr hDimension hX
    sourceAction hSourceAction centered hCentered hSum hCenteredEquiv
  refine ⟨x,?_⟩
  intro i j
  have hi:=congrFun hx i
  have hj:=congrFun hx j
  change score x i-average x=0 at hi
  change score x j-average x=0 at hj
  linarith

end FairDivision.Topology.Volovikov
