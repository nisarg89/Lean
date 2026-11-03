import FairDivision.Topology.Volovikov.OddPrimeElementaryObstruction
import FairDivision.Topology.Volovikov.OddPrimeConnectedObstruction

/-!
# Prime-power connected-source obstruction and score zeros

The general odd-prime/rank finite-join theorem now discharges the same
existing geometric transfer as the prime and mod-two special cases.
The public result is stated for the literal p-torus position action and
the literal ReducedSphere coordinates used by BF. The p=2 branch reuses
its earlier direct real Fourier proof.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open scoped BigOperators
open FairDivision.Topology FairDivision.Topology.NerveConnectivity

/-- The actual connected-source reduced regular obstruction at every odd
prime power, with positive elementary-abelian rank. -/
theorem no_reducedSphere_map_odd_primePower
    {p r k : ℕ} [Fact p.Prime] {X : Type*} [TopologicalSpace X]
    (hp : p≠2) (hr : 0<r) (hDimension : p^r≤k+2) (hX : NullConnectedSpace k X)
    (sourceAction : (Fin r→ZMod p)→X≃ₜX)
    (hSourceAction : IsContinuousAddAction sourceAction)
    (F : X→ReducedSphere (p^r)) (hContinuous : Continuous F)
    (hEquivariant : ∀a x,F (sourceAction a x)=
      relabelReducedSphere (pTorusPositionPerm p r a) (F x)) : False :=
  no_reducedSphere_connectedMap_of_finiteObstruction (pTorusPositionEquiv p r)
    hDimension hX sourceAction hSourceAction
    (complexFiniteJoinNoMap_odd_primePower p r hp hr) F hContinuous hEquivariant

/-- Full prime-power position-action obstruction. No topological or
cohomological obstruction remains as an assumption. -/
theorem no_reducedSphere_map_primePower
    {p r k : ℕ} [Fact p.Prime] {X : Type*} [TopologicalSpace X]
    (hr : 0<r) (hDimension : p^r≤k+2) (hX : NullConnectedSpace k X)
    (sourceAction : (Fin r→ZMod p)→X≃ₜX)
    (hSourceAction : IsContinuousAddAction sourceAction)
    (F : X→ReducedSphere (p^r)) (hContinuous : Continuous F)
    (hEquivariant : ∀a x,F (sourceAction a x)=
      relabelReducedSphere (pTorusPositionPerm p r a) (F x)) : False := by
  by_cases hp : p=2
  · subst p
    exact no_reducedSphere_map_modTwo hr hDimension hX
      sourceAction hSourceAction F hContinuous hEquivariant
  · exact no_reducedSphere_map_odd_primePower hp hr hDimension hX
      sourceAction hSourceAction F hContinuous hEquivariant

/-- The existing zero-vector normalization now has its prime-power
obstruction premise discharged by actual source proofs. -/
theorem exists_centered_position_zero_primePower
    {p r k : ℕ} [Fact p.Prime] {X : Type*} [TopologicalSpace X]
    (hr : 0<r) (hDimension : p^r≤k+2) (hX : NullConnectedSpace k X)
    (sourceAction : (Fin r→ZMod p)→X≃ₜX)
    (hSourceAction : IsContinuousAddAction sourceAction)
    (score : X→Fin (p^r)→ℝ) (hContinuous : Continuous score)
    (hCenter : ∀x,∑i : Fin (p^r),score x i=0)
    (hEquivariant : ∀a x i,
      score (sourceAction a x) (pTorusPositionPerm p r a i)=score x i) :
    ∃x,score x=0 := by
  apply zero_of_reducedSphere_obstruction (fun a x=>sourceAction a x)
    (pTorusPositionPerm p r) score hContinuous hCenter hEquivariant
  intro F hF hEq
  exact no_reducedSphere_map_primePower hr hDimension hX
    sourceAction hSourceAction F hF hEq

/-- Equalization by subtracting the coordinate mean. All original
coordinates are retained; no Fourier encoding is exposed to BF readers. -/
theorem exists_equal_position_scores_primePower
    {p r k : ℕ} [Fact p.Prime] {X : Type*} [TopologicalSpace X]
    (hr : 0<r) (hDimension : p^r≤k+2) (hX : NullConnectedSpace k X)
    (sourceAction : (Fin r→ZMod p)→X≃ₜX)
    (hSourceAction : IsContinuousAddAction sourceAction)
    (score : X→Fin (p^r)→ℝ) (hContinuous : Continuous score)
    (hEquivariant : ∀a x i,
      score (sourceAction a x) (pTorusPositionPerm p r a i)=score x i) :
    ∃x,∀i j,score x i=score x j := by
  let average : X→ℝ:=fun x=>(∑i : Fin (p^r),score x i)/(p^r : ℕ)
  let centered : X→Fin (p^r)→ℝ:=fun x i=>score x i-average x
  have hn : ((p^r : ℕ) : ℝ)≠0 := by
    exact_mod_cast pow_ne_zero r (Fact.out : p.Prime).ne_zero
  have hAverage : Continuous average :=
    (continuous_finset_sum _ (fun i hi=>(continuous_apply i).comp hContinuous)).div_const _
  have hCentered : Continuous centered := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp hContinuous).sub hAverage
  have hSum : ∀x,∑i : Fin (p^r),centered x i=0 := by
    intro x
    simp only [centered,average,Finset.sum_sub_distrib,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp [hn] <;> ring
  have hAverageEquiv : ∀a x,average (sourceAction a x)=average x := by
    intro a x
    unfold average
    congr 1
    calc
      (∑i : Fin (p^r),score (sourceAction a x) i)=
          ∑i : Fin (p^r),score (sourceAction a x) (pTorusPositionPerm p r a i) :=
        (Equiv.sum_comp (pTorusPositionPerm p r a) _).symm
      _=∑i : Fin (p^r),score x i := Finset.sum_congr rfl (fun i hi=>hEquivariant a x i)
  have hCenteredEquiv : ∀a x i,
      centered (sourceAction a x) (pTorusPositionPerm p r a i)=centered x i := by
    intro a x i
    simp only [centered,hEquivariant,hAverageEquiv]
  obtain ⟨x,hx⟩:=exists_centered_position_zero_primePower hr hDimension hX
    sourceAction hSourceAction centered hCentered hSum hCenteredEquiv
  refine ⟨x,?_⟩
  intro i j
  have hi:=congrFun hx i
  have hj:=congrFun hx j
  change score x i-average x=0 at hi
  change score x j-average x=0 at hj
  linarith

end FairDivision.Topology.Volovikov
