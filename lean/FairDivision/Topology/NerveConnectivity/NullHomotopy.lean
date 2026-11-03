import FairDivision.Topology.NerveConnectivity.Basic
import Mathlib.Topology.Homotopy.Equiv

/-!
# Operational connectivity through nullhomotopies

For finite-complex topology, it is convenient to say directly that every map
from each low-dimensional sphere is nullhomotopic. We model the sphere as the
boundary of a cube. This predicate is used separately from `ConnectedThrough`;
no equivalence between the two is assumed in a certificate.
-/

set_option autoImplicit false

open scoped unitInterval Topology

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- The boundary of a `(j+1)`-dimensional cube, a model of the `j`-sphere. -/
abbrev CubeSphere (j : ℕ) :=
  {p : I^ (Fin (j + 1)) // p ∈ Cube.boundary (Fin (j + 1))}

/-- Every map from a cube-boundary sphere of dimension at most `k` is freely
nullhomotopic. Nonemptiness is included because sphere-map conditions alone
would hold vacuously for the empty space. -/
def NullConnectedSpace (k : ℕ) (X : Type u) [TopologicalSpace X] : Prop :=
  Nonempty X ∧
    ∀ (j : ℕ), j ≤ k → ∀ f : C(CubeSphere j, X),
      ∃ x : X, f.Homotopic (ContinuousMap.const _ x)

/-- The operational predicate for a subspace with the subtype topology. -/
def NullConnectedSet {X : Type u} [TopologicalSpace X]
    (k : ℕ) (S : Set X) : Prop :=
  NullConnectedSpace k S

/-- Lower-dimensional nullhomotopy connectivity follows immediately. -/
theorem NullConnectedSpace.mono {X : Type u} [TopologicalSpace X]
    {k l : ℕ} (hX : NullConnectedSpace k X) (hlk : l ≤ k) :
    NullConnectedSpace l X := by
  refine ⟨hX.1, ?_⟩
  intro j hj f
  exact hX.2 j (hj.trans hlk) f

/-- Nullhomotopy connectivity is invariant under a homotopy equivalence.
This is the transfer needed after a simplicial deformation retraction. -/
theorem NullConnectedSpace.ofHomotopyEquiv
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {k : ℕ} (h : ContinuousMap.HomotopyEquiv X Y)
    (hX : NullConnectedSpace k X) : NullConnectedSpace k Y := by
  refine ⟨⟨h.toFun (Classical.choice hX.1)⟩, ?_⟩
  intro j hj f
  obtain ⟨x, hx⟩ := hX.2 j hj (h.invFun.comp f)
  refine ⟨h.toFun x, ?_⟩
  have hright : f.Homotopic (h.toFun.comp (h.invFun.comp f)) := by
    have h' := (ContinuousMap.Homotopic.comp h.right_inv
      (ContinuousMap.Homotopic.refl f)).symm
    simpa [ContinuousMap.comp_assoc] using h'
  have hforward : (h.toFun.comp (h.invFun.comp f)).Homotopic
      (ContinuousMap.const _ (h.toFun x)) := by
    have h' := ContinuousMap.Homotopic.comp
      (ContinuousMap.Homotopic.refl h.toFun) hx
    simpa [ContinuousMap.comp_assoc] using h'
  exact hright.trans hforward

/-- Both directions of homotopy-equivalence invariance. -/
theorem nullConnectedSpace_congr
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {k : ℕ} (h : ContinuousMap.HomotopyEquiv X Y) :
    NullConnectedSpace k X ↔ NullConnectedSpace k Y :=
  ⟨NullConnectedSpace.ofHomotopyEquiv h, NullConnectedSpace.ofHomotopyEquiv h.symm⟩

/-- A retraction with a homotopy back to the identity is a homotopy
equivalence. The pointwise fixed-set condition of a strong deformation
retraction is stronger than needed here. -/
def homotopyEquivOfRetraction
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (r : C(X, Y)) (i : C(Y, X))
    (hri : r.comp i = ContinuousMap.id Y)
    (hir : (i.comp r).Homotopic (ContinuousMap.id X)) :
    ContinuousMap.HomotopyEquiv X Y where
  toFun := r
  invFun := i
  left_inv := hir
  right_inv := by
    simpa only [hri] using (ContinuousMap.Homotopic.refl (ContinuousMap.id Y))

/-- Transfer nullhomotopy connectivity from a deformation retract to the
ambient space. -/
theorem NullConnectedSpace.ofRetraction
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {k : ℕ} (r : C(X, Y)) (i : C(Y, X))
    (hri : r.comp i = ContinuousMap.id Y)
    (hir : (i.comp r).Homotopic (ContinuousMap.id X))
    (hY : NullConnectedSpace k Y) : NullConnectedSpace k X :=
  NullConnectedSpace.ofHomotopyEquiv
    (homotopyEquivOfRetraction r i hri hir).symm hY

end FairDivision.Topology.NerveConnectivity
