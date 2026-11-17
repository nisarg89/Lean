import FairDivision.Topology.FiniteSimplexCubeBoundary
import FairDivision.Topology.NerveConnectivity.ConeExtension

/-!
# Filling the attaching boundary of a finite simplex

The operational connectivity predicate is stated using cube-boundary spheres.
The shared geometric homeomorphism transports that statement to the attaching
boundary of each finite simplex, and the cone-extension theorem produces a
continuous filling on the topological cone of that boundary. A later module
identifies the cone with the simplex cell itself and pastes orbitwise fillings.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity
open scoped unitInterval Topology

/-- Every positive-dimensional finite simplex has a nonempty boundary. -/
theorem finiteStandardSimplexBoundary_nonempty (j : ℕ) :
    Nonempty (finiteStandardSimplexBoundary j) := by
  let v : Fin (j + 2) := ⟨0, by omega⟩
  let w : Fin (j + 2) := ⟨1, by omega⟩
  have hvw : v ≠ w := by
    intro h
    have := congrArg Fin.val h
    norm_num [v, w] at this
  let x : stdSimplex ℝ (Fin (j + 2)) := stdSimplex.vertex v
  refine ⟨⟨x, w, ?_⟩⟩
  simp [x, stdSimplex.vertex, Pi.single_apply, hvw.symm]

/-- Nullhomotopy of a simplex-boundary map follows from the operational
cube-sphere connectivity predicate. -/
theorem simplexBoundary_homotopic_const
    {X : Type*} [TopologicalSpace X] {k j : ℕ}
    (hX : NullConnectedSpace k X) (hj : j ≤ k)
    (f : C(finiteStandardSimplexBoundary j, X)) :
    ∃ x : X, f.Homotopic (ContinuousMap.const _ x) := by
  let e := finiteSimplexBoundaryCubeSphereHomeomorph j
  let g : C(CubeSphere j, X) := f.comp ⟨e.symm, e.symm.continuous⟩
  obtain ⟨x, hg⟩ := hX.2 j hj g
  have hcomp := hg.comp (ContinuousMap.Homotopic.refl ⟨e, e.continuous⟩)
  have hleft : g.comp ⟨e, e.continuous⟩ = f := by
    ext s
    simp [g, e]
  have hright : (ContinuousMap.const (CubeSphere j) x).comp ⟨e, e.continuous⟩ =
      ContinuousMap.const (finiteStandardSimplexBoundary j) x := by
    ext s
    rfl
  rw [hleft, hright] at hcomp
  exact ⟨x, hcomp⟩

/-- A simplex-boundary map extends over the cone on that boundary whenever
the target is operationally connected in the required dimension. -/
theorem exists_simplexBoundary_coneFilling
    {X : Type*} [TopologicalSpace X] {k j : ℕ}
    (hX : NullConnectedSpace k X) (hj : j ≤ k)
    (f : C(finiteStandardSimplexBoundary j, X)) :
    ∃ F : C(TopologicalCone (finiteStandardSimplexBoundary j), X),
      F.comp (coneBase (finiteStandardSimplexBoundary j)) = f := by
  letI : Nonempty (finiteStandardSimplexBoundary j) :=
    finiteStandardSimplexBoundary_nonempty j
  exact (homotopic_const_iff_coneExtension f).mp
    (simplexBoundary_homotopic_const hX hj f)

end FairDivision.Topology.Volovikov
