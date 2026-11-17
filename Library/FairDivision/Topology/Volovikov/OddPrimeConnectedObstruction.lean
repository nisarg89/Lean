import FairDivision.Topology.Volovikov.OddPrimeCyclicObstruction
import FairDivision.Topology.Volovikov.UniversalJoinEquivariantTransfer
import FairDivision.Topology.Volovikov.AssociatedOrbitSection
import FairDivision.Topology.Volovikov.ZeroReduction
import FairDivision.Topology.Volovikov.ModTwoConnectedObstruction

/-!
# Odd-prime connected-source sphere obstruction and score zeros

The same existing cellular transfer sends p source join factors into a
sufficiently connected space. The finite cyclic obstruction then rules out
an equivariant reduced-sphere map. The rank-one p-torus statements below
use exactly the position permutation in the manuscript score reductions.
The odd-prime rank-greater-than-one theorem is not asserted here.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology FairDivision.Topology.NerveConnectivity

/-- Geometric transfer applied to any proved finite complex obstruction.
Only this composition is generic; the odd cyclic premise is discharged
unconditionally in the next theorem. -/
theorem no_reducedSphere_connectedMap_of_finiteObstruction
    {n k : ℕ} {G X : Type*} [AddCommGroup G] [Fintype G] [TopologicalSpace X]
    (e : Fin n≃G) (hDimension : n≤k+2) (hX : NullConnectedSpace k X)
    (sourceAction : G→X≃ₜX) (hSourceAction : IsContinuousAddAction sourceAction)
    (hObstruction : ComplexFiniteJoinNoMap n G)
    (F : X→ReducedSphere n) (hContinuous : Continuous F)
    (hEquivariant : ∀a x,F (sourceAction a x)=
      relabelReducedSphere (regularPositionPerm e a) (F x)) : False := by
  obtain ⟨transfer,hTransfer⟩:=exists_equivariant_universalJoinMap
    (m:=n) hDimension hX sourceAction hSourceAction
  apply no_reducedSphere_joinMap_of_complexJoinNoMap e
    (complexJoinNoMap_of_finiteJoinNoMap hObstruction)
    ((⟨F,hContinuous⟩ : C(X, ReducedSphere n)).comp transfer)
  intro a x
  have hTranslate : transfer (translateJoinRealization a x)=sourceAction a (transfer x) := by
    simpa only [translateInvariant_universal_eq_join] using hTransfer a x
  change F (transfer (translateJoinRealization a x))=_
  rw [hTranslate]
  exact hEquivariant a (transfer x)

/-- The connected-source obstruction for the actual rank-one p-torus
position action. There is no residual no-map or cohomology hypothesis. -/
theorem no_reducedSphere_map_odd_prime_rank_one
    {p k : ℕ} [Fact p.Prime] {X : Type*} [TopologicalSpace X]
    (hp : p≠2) (hDimension : p^1≤k+2) (hX : NullConnectedSpace k X)
    (sourceAction : (Fin 1→ZMod p)→X≃ₜX)
    (hSourceAction : IsContinuousAddAction sourceAction)
    (F : X→ReducedSphere (p^1)) (hContinuous : Continuous F)
    (hEquivariant : ∀a x,F (sourceAction a x)=
      relabelReducedSphere (pTorusPositionPerm p 1 a) (F x)) : False := by
  refine no_reducedSphere_connectedMap_of_finiteObstruction
    (pTorusPositionEquiv p 1) hDimension hX sourceAction hSourceAction
    ?_ F hContinuous hEquivariant
  simpa only [pow_one] using complexFiniteJoinNoMap_odd_prime_rank_one p hp

/-- All cyclic primes, including the already proved mod-two case. -/
theorem no_reducedSphere_map_prime_rank_one
    {p k : ℕ} [Fact p.Prime] {X : Type*} [TopologicalSpace X]
    (hDimension : p^1≤k+2) (hX : NullConnectedSpace k X)
    (sourceAction : (Fin 1→ZMod p)→X≃ₜX)
    (hSourceAction : IsContinuousAddAction sourceAction)
    (F : X→ReducedSphere (p^1)) (hContinuous : Continuous F)
    (hEquivariant : ∀a x,F (sourceAction a x)=
      relabelReducedSphere (pTorusPositionPerm p 1 a) (F x)) : False := by
  by_cases hp : p=2
  · subst p
    exact no_reducedSphere_map_modTwo (by decide : 0<1) hDimension hX
      sourceAction hSourceAction F hContinuous hEquivariant
  · exact no_reducedSphere_map_odd_prime_rank_one hp hDimension hX
      sourceAction hSourceAction F hContinuous hEquivariant

/-- The already proved normalization reduction gives an actual zero of a
centered score vector on every sufficiently connected rank-one p-space. -/
theorem exists_centered_position_zero_odd_prime
    {p k : ℕ} [Fact p.Prime] {X : Type*} [TopologicalSpace X]
    (hp : p≠2) (hDimension : p^1≤k+2) (hX : NullConnectedSpace k X)
    (sourceAction : (Fin 1→ZMod p)→X≃ₜX)
    (hSourceAction : IsContinuousAddAction sourceAction)
    (score : X→Fin (p^1)→ℝ) (hContinuous : Continuous score)
    (hCenter : ∀x,∑i : Fin (p^1),score x i=0)
    (hEquivariant : ∀a x i,
      score (sourceAction a x) (pTorusPositionPerm p 1 a i)=score x i) :
    ∃x,score x=0 := by
  apply zero_of_reducedSphere_obstruction (fun a x=>sourceAction a x)
    (pTorusPositionPerm p 1) score hContinuous hCenter hEquivariant
  intro F hF hEq
  exact no_reducedSphere_map_odd_prime_rank_one hp hDimension hX
    sourceAction hSourceAction F hF hEq

/-- Subtracting the coordinate mean yields equalization of every original
score, with the same continuous action and the same connectivity bound. -/
theorem exists_equal_position_scores_odd_prime
    {p k : ℕ} [Fact p.Prime] {X : Type*} [TopologicalSpace X]
    (hp : p≠2) (hDimension : p^1≤k+2) (hX : NullConnectedSpace k X)
    (sourceAction : (Fin 1→ZMod p)→X≃ₜX)
    (hSourceAction : IsContinuousAddAction sourceAction)
    (score : X→Fin (p^1)→ℝ) (hContinuous : Continuous score)
    (hEquivariant : ∀a x i,
      score (sourceAction a x) (pTorusPositionPerm p 1 a i)=score x i) :
    ∃x,∀i j,score x i=score x j := by
  let average : X→ℝ:=fun x=>(∑i : Fin (p^1),score x i)/(p^1 : ℕ)
  let centered : X→Fin (p^1)→ℝ:=fun x i=>score x i-average x
  have hn : ((p^1 : ℕ) : ℝ)≠0 := by
    exact_mod_cast pow_ne_zero 1 (Fact.out : p.Prime).ne_zero
  have hAverage : Continuous average :=
    (continuous_finset_sum _ (fun i hi=>(continuous_apply i).comp hContinuous)).div_const _
  have hCentered : Continuous centered := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp hContinuous).sub hAverage
  have hSum : ∀x,∑i : Fin (p^1),centered x i=0 := by
    intro x
    simp only [centered,average,Finset.sum_sub_distrib,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp [hn] <;> ring
  have hAverageEquiv : ∀a x,average (sourceAction a x)=average x := by
    intro a x
    unfold average
    congr 1
    calc
      (∑i : Fin (p^1),score (sourceAction a x) i)=
          ∑i : Fin (p^1),score (sourceAction a x) (pTorusPositionPerm p 1 a i) :=
        (Equiv.sum_comp (pTorusPositionPerm p 1 a) _).symm
      _=∑i : Fin (p^1),score x i := Finset.sum_congr rfl (fun i hi=>hEquivariant a x i)
  have hCenteredEquiv : ∀a x i,
      centered (sourceAction a x) (pTorusPositionPerm p 1 a i)=centered x i := by
    intro a x i
    simp only [centered,hEquivariant,hAverageEquiv]
  obtain ⟨x,hx⟩:=exists_centered_position_zero_odd_prime hp hDimension hX
    sourceAction hSourceAction centered hCentered hSum hCenteredEquiv
  refine ⟨x,?_⟩
  intro i j
  have hi:=congrFun hx i
  have hj:=congrFun hx j
  change score x i-average x=0 at hi
  change score x j-average x=0 at hj
  linarith

end FairDivision.Topology.Volovikov
