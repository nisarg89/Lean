import FairDivision.Topology.Volovikov.ShiftedCyclicApproximation

/-!
# General-prime elementary-abelian no-map theorem for twisted cyclic joins

This is the actual geometric endpoint of the shifted-cyclic proof. Every
occupied target color carries a nonzero elementary character, but no
single genuine generator need move all colors. The common generic shift
acts on source and target chains. Subdivision makes the literal source
cone sequence small enough for vertex-selection approximation; the
completed target algebraic obstruction then gives a contradiction.

The compactness, subdivision shrinkage, and oriented approximation
lemmas are reused from the pinned DKGM source. No cohomology or Euler
class statement is postulated, and the original BF source/paper is not
changed by this proof of an external topological dependency.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.Volovikov.ShiftedCyclicJoinObstruction

open scoped BigOperators
open Dvoretzky Dvoretzky.Dold
open OddPrimeTensorSource (Group generator)
open OddPrimeTwistedJoinChains (Label)
open ShiftedCyclicSupportMatrices (GenericField weights)
open ShiftedCyclicApproximation

/-- General elementary-abelian obstruction, for EVERY prime and rank.
Each color may be moved by a different genuine generator. -/
theorem no_twisted_join_map (p r : ℕ) [Fact p.Prime] {N D : ℕ}
    (hDimension : D+1<N)
    (ε : Fin r→Fin (D+1)→ZMod p)
    (hCharacters : ∀j : Fin (D+1),∃q : Fin r,ε q j≠0)
    (Φ : (Fin N→Group p r→ℝ)→Fin (D+1)→Label p→ℝ)
    (hContinuous : ContinuousOn Φ (GroupJoin (Group p r) N))
    (hMaps : ∀x∈GroupJoin (Group p r) N,Φ x∈GroupJoin (Label p) (D+1))
    (hEq : ∀q : Fin r,∀x∈GroupJoin (Group p r) N,
      Φ (joinAct (generator (p:=p) q) x)=pointShift (ε q) (Φ x)) : False := by
  classical
  let K:=GenericField p r
  let «λ» : Fin r→K:=weights
  let c : ℕ→ShiftedCyclicSource.SourceChain p r N K:=
    ShiftedCyclicSource.sequence p r N K «λ»
  have hUniform : UniformContinuousOn Φ (GroupJoin (Group p r) N) :=
    (isCompact_groupJoin (G:=Group p r) N).uniformContinuousOn_of_continuous hContinuous
  have hPositive : (0 : ℝ)<1/(2*(D+1)):=by positivity
  obtain ⟨δ,hδPositive,hδ⟩:=Metric.uniformContinuousOn_iff.mp hUniform _ hPositive
  let q : ℝ:=(D+1)/(D+2)
  have hqNonnegative : 0≤q:=by dsimp [q];positivity
  have hqLess : q<1:=by dsimp [q];rw [div_lt_one (by positivity)];linarith
  obtain ⟨iterations,hSmall⟩:=exists_pow_lt_of_lt_one hδPositive hqLess
  let S : Module.End K (ShiftedCyclicSource.SourceChain p r N K):=sd^iterations
  have hGood : ∀k≤D+1,S (c k)∈Finsupp.supported K K
      {l | l.length=k+1 ∧ (∀y∈l,y∈GroupJoin (Group p r) N) ∧
        Consistent (l.map (vtxSel Φ))} := by
    intro k hk
    rw [Finsupp.mem_supported]
    intro l hl
    obtain ⟨l₀,hl₀,hMap⟩:=mem_support_map hl
    have hV : VList N k l₀:=
      ShiftedCyclicSource.sequence_supported p r N K «λ» k hl₀
    obtain ⟨hLength,hHull,hDistance⟩:=sdIter_support iterations l₀ 1 hV.dist_le l hMap
    have hOriginalLength:=hV.length_eq
    have hJoin : ∀y∈l,y∈GroupJoin (Group p r) N :=
      fun y hy=>hV.hull_subset (by omega) (hHull y hy)
    refine ⟨by rw [hLength,hOriginalLength],hJoin,
      consistent_of_close Φ hMaps hδ hJoin (fun y hy z hz=>?_)⟩
    apply lt_of_le_of_lt (hDistance y hy z hz)
    apply lt_of_le_of_lt ?_ hSmall
    rw [mul_one,hOriginalLength]
    apply pow_le_pow_left₀ (ratio_nonneg (k+1))
    dsimp [q]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hkReal : (k : ℝ)≤D+1:=by exact_mod_cast hk
    push_cast
    nlinarith
  have hConsistent : ∀k≤D+1,S (c k)∈Finsupp.supported K K
      {l | Consistent (l.map (vtxSel Φ))} :=
    fun k hk=>Finsupp.supported_mono (fun l hl=>hl.2.2) (hGood k hk)
  have hInJoin : ∀k≤D+1,S (c k)∈Finsupp.supported K K
      {l | ∀y∈l,y∈GroupJoin (Group p r) N} :=
    fun k hk=>Finsupp.supported_mono (fun l hl=>hl.2.1) (hGood k hk)
  have hBoundarySubdivision : Commute
      (bd : Module.End K (ShiftedCyclicSource.SourceChain p r N K)) S :=
    Commute.pow_right (LinearMap.ext (fun z=>bd_sd z)) iterations
  have hEmpty : S (ShiftedCyclicSource.empty p r N K)=
      ShiftedCyclicSource.empty p r N K := by
    change ((sd : Module.End K (ShiftedCyclicSource.SourceChain p r N K))^iterations)
      (ShiftedCyclicSource.empty p r N K)=_
    clear hBoundarySubdivision hInJoin hConsistent hGood S hSmall
    induction iterations with
    | zero=>rfl
    | succ k ih=>rw [pow_succ',Module.End.mul_apply,ih,
        ShiftedCyclicSource.empty,sd_single,sdList_nil,one_smul]
  apply ShiftedCyclicTarget.no_sequence ε hCharacters (D+1)
    (fun k=>psi Φ (S (c k)))
  · rw [←psi_boundary Φ (hConsistent 0 (by omega)),←Module.End.mul_apply,
      hBoundarySubdivision.eq,Module.End.mul_apply,
      ShiftedCyclicSource.boundary_sequence_zero,hEmpty,ShiftedCyclicSource.empty,psi_single]
    rfl
  · intro k hk
    rw [←psi_boundary Φ (hConsistent (k+1) (by omega)),←Module.End.mul_apply,
      hBoundarySubdivision.eq,Module.End.mul_apply,
      ShiftedCyclicSource.boundary_sequence_succ,←Module.End.mul_apply,
      (ShiftedCyclicSource.subdivision_rho p r N K «λ» iterations k).eq,
      Module.End.mul_apply]
    exact psi_rho Φ ε hMaps hEq k (hInJoin k (by omega))
  · apply eq_on_supported (psi Φ) 0 (fun l hl=>?_) (hGood (D+1) le_rfl)
    rw [psi_single,LinearMap.zero_apply]
    exact alpha_eq_zero_of_length hl.2.2 (by rw [List.length_map,hl.1];omega)

/-- Arbitrary positive target-color count, retaining the exact upstream
D+1 endpoint internally. -/
theorem no_twisted_join_map_positive (p r : ℕ) [Fact p.Prime] {N M : ℕ}
    (hM : 0<M) (hDimension : M<N)
    (ε : Fin r→Fin M→ZMod p)
    (hCharacters : ∀j : Fin M,∃q : Fin r,ε q j≠0)
    (Φ : (Fin N→Group p r→ℝ)→Fin M→Label p→ℝ)
    (hContinuous : ContinuousOn Φ (GroupJoin (Group p r) N))
    (hMaps : ∀x∈GroupJoin (Group p r) N,Φ x∈GroupJoin (Label p) M)
    (hEq : ∀q : Fin r,∀x∈GroupJoin (Group p r) N,
      Φ (joinAct (generator (p:=p) q) x)=pointShift (ε q) (Φ x)) : False := by
  cases M with
  | zero=>omega
  | succ D=>exact no_twisted_join_map p r hDimension ε hCharacters Φ hContinuous hMaps hEq

end FairDivision.Topology.Volovikov.ShiftedCyclicJoinObstruction
