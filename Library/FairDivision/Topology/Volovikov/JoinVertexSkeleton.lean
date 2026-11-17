import FairDivision.Topology.Volovikov.JoinOrbitExtension

/-!
# The equivariant vertex-skeleton map

The one-vertex skeleton of a finite universal join is a finite discrete
space, with one point for each join vertex. A chosen target point extends
along the group action to an equivariant map on this skeleton.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity
open scoped Classical

/-- The probability-vector vertex lies in the one-vertex skeleton. -/
noncomputable def oneSkeletonVertex {m : ℕ} {G : Type*}
    [Fintype G] (v : Fin m × G) :
    simplicialRealization (universalJoinSkeleton m G 1) := by
  classical
  refine ⟨stdSimplex.vertex v, ?_⟩
  have hs : FairDivision.Topology.finiteSimplexSupport
      (stdSimplex.vertex (S := ℝ) v) = {v} := by
    ext u
    simp only [FairDivision.Topology.finiteSimplexSupport,
      Finset.mem_filter, Finset.mem_univ, true_and,
      stdSimplex.vertex_coe, Pi.single_apply, Finset.mem_singleton]
    split_ifs <;> simp_all
  change FairDivision.Topology.finiteSimplexSupport
    (stdSimplex.vertex v) ∈ universalJoinSkeleton m G 1
  rw [hs]
  constructor
  · constructor
    · simp
    · intro i g h hgi hhi
      have hvg : (i, g) = v := by simpa using hgi
      have hvh : (i, h) = v := by simpa using hhi
      exact congrArg Prod.snd (hvg.trans hvh.symm)
  · simp

/-- Every point of the one-vertex skeleton is a simplex vertex. -/
theorem exists_oneSkeletonVertex {m : ℕ} {G : Type*}
    [Fintype G]
    (w : simplicialRealization (universalJoinSkeleton m G 1)) :
    ∃ v : Fin m × G, oneSkeletonVertex v = w := by
  classical
  have hne := w.2.1.1
  have hcard : (FairDivision.Topology.finiteSimplexSupport w.1).card = 1 := by
    have hpos := Finset.card_pos.mpr hne
    have hle := w.2.2
    omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
  refine ⟨v, Subtype.ext ?_⟩
  apply stdSimplex.ext
  funext u
  have hzero (x : Fin m × G) (hxv : x ≠ v) : w.1.1 x = 0 := by
    have hnot : x ∉ FairDivision.Topology.finiteSimplexSupport w.1 := by
      rw [hv]
      simpa using hxv
    have hnpos : ¬ 0 < w.1.1 x := by
      intro hpos
      exact hnot ((FairDivision.Topology.mem_finiteSimplexSupport_iff _ _).2 hpos)
    exact le_antisymm (le_of_not_gt hnpos) (w.1.2.1 x)
  have hvone : w.1.1 v = 1 := by
    have hsum : (∑ x : Fin m × G, w.1.1 x) = w.1.1 v := by
      apply Finset.sum_eq_single v
      · intro x _ hxv
        exact hzero x hxv
      · simp
    rw [← hsum]
    exact w.1.2.2
  simp only [oneSkeletonVertex, stdSimplex.vertex_coe, Pi.single_apply]
  change (if u = v then (1 : ℝ) else 0) = w.1.1 u
  by_cases huv : u = v
  · subst u
    simpa using hvone.symm
  · simpa [huv] using (hzero u huv).symm

/-- Distinct join vertices give distinct one-skeleton points. -/
theorem oneSkeletonVertex_injective {m : ℕ} {G : Type*}
    [Fintype G] :
    Function.Injective (oneSkeletonVertex (m := m) (G := G)) := by
  intro v w h
  exact stdSimplex.vertex_injective (congrArg Subtype.val h)

/-- The one-vertex skeleton is finite and therefore discrete. -/
theorem oneSkeleton_discreteTopology {m : ℕ} {G : Type*}
    [Fintype G] :
    DiscreteTopology (simplicialRealization
      (universalJoinSkeleton m G 1)) := by
  classical
  haveI : Finite (simplicialRealization
      (universalJoinSkeleton m G 1)) :=
    Finite.of_surjective oneSkeletonVertex exists_oneSkeletonVertex
  exact DiscreteTopology.of_finite_of_isClosed_singleton
    (fun _ => isClosed_singleton)

/-- Choose the unique join vertex corresponding to a one-skeleton point. -/
noncomputable def oneSkeletonVertexOfPoint {m : ℕ} {G : Type*}
    [Fintype G]
    (w : simplicialRealization (universalJoinSkeleton m G 1)) :
    Fin m × G :=
  Classical.choose (exists_oneSkeletonVertex w)

/-- The chosen vertex reconstructs the one-skeleton point. -/
theorem oneSkeletonVertexOfPoint_spec {m : ℕ} {G : Type*}
    [Fintype G]
    (w : simplicialRealization (universalJoinSkeleton m G 1)) :
    oneSkeletonVertex (oneSkeletonVertexOfPoint w) = w :=
  Classical.choose_spec (exists_oneSkeletonVertex w)

/-- Translation carries a vertex point to its translated vertex. -/
theorem translate_oneSkeletonVertex {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G] (a : G) (v : Fin m × G) :
    translateInvariantRealization
      (universalJoinSkeleton m G 1)
      universalJoinSkeleton_invariant a (oneSkeletonVertex v) =
      oneSkeletonVertex (translateJoinVertex a v) := by
  apply Subtype.ext
  change stdSimplex.map (translateJoinVertex a)
      (stdSimplex.vertex v) =
      stdSimplex.vertex (translateJoinVertex a v)
  exact stdSimplex.map_vertex _ _

/-- The vertex chosen from a translated one-skeleton point is the
translation of its original chosen vertex. -/
theorem oneSkeletonVertexOfPoint_translate {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G] (a : G)
    (w : simplicialRealization (universalJoinSkeleton m G 1)) :
    oneSkeletonVertexOfPoint
      (translateInvariantRealization
        (universalJoinSkeleton m G 1)
        universalJoinSkeleton_invariant a w) =
      translateJoinVertex a (oneSkeletonVertexOfPoint w) := by
  apply oneSkeletonVertex_injective
  rw [oneSkeletonVertexOfPoint_spec,
    ← translate_oneSkeletonVertex,
    oneSkeletonVertexOfPoint_spec]

/-- A point of the target determines an equivariant map on the vertex
skeleton of the finite universal join. -/
noncomputable def equivariantVertexSkeletonMap
    {m : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (targetAction : G → X ≃ₜ X) (x0 : X) :
    C(simplicialRealization (universalJoinSkeleton m G 1), X) := by
  letI : DiscreteTopology (simplicialRealization
      (universalJoinSkeleton m G 1)) := oneSkeleton_discreteTopology
  exact ⟨(fun w => targetAction (oneSkeletonVertexOfPoint w).2 x0),
    continuous_of_discreteTopology⟩

/-- The vertex-skeleton map respects translation on its source and target. -/
theorem equivariantVertexSkeletonMap_equivariant
    {m : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (targetAction : G → X ≃ₜ X)
    (hAction : IsContinuousAddAction targetAction) (x0 : X) :
    IsEquivariantJoinMap (universalJoinSkeleton m G 1)
      universalJoinSkeleton_invariant targetAction
      (equivariantVertexSkeletonMap targetAction x0) := by
  intro a w
  change targetAction
      (oneSkeletonVertexOfPoint
        (translateInvariantRealization
          (universalJoinSkeleton m G 1)
          universalJoinSkeleton_invariant a w)).2 x0 =
    targetAction a (targetAction (oneSkeletonVertexOfPoint w).2 x0)
  rw [oneSkeletonVertexOfPoint_translate]
  exact hAction.2 a (oneSkeletonVertexOfPoint w).2 x0

end FairDivision.Topology.Volovikov
