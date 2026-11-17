import FairDivision.Topology.NerveConnectivity.NullHomotopy
import Mathlib.Topology.Connected.PathConnected

/-!
# The zero-dimensional case of nullhomotopy connectivity

The boundary of the one-dimensional cube is a two-point discrete space.
Consequently, every map from it being nullhomotopic is equivalent to path
connectedness. This gives the operational connectivity predicate the correct
base case for a finite-cover induction.
-/

set_option autoImplicit false

open scoped unitInterval Topology

namespace FairDivision.Topology.NerveConnectivity

universe u

private def sphereZeroLeft : CubeSphere 0 :=
  ⟨fun _ => 0, ⟨0, Or.inl rfl⟩⟩

private def sphereZeroRight : CubeSphere 0 :=
  ⟨fun _ => 1, ⟨0, Or.inr rfl⟩⟩

private theorem sphereZero_eq_left_or_right (p : CubeSphere 0) :
    p = sphereZeroLeft ∨ p = sphereZeroRight := by
  obtain ⟨i, hi⟩ := p.2
  have hi0 : i = 0 := Fin.fin_one_eq_zero i
  subst i
  rcases hi with h0 | h1
  · left
    apply Subtype.ext
    funext j
    have hj0 : j = 0 := Fin.fin_one_eq_zero j
    subst j
    exact h0
  · right
    apply Subtype.ext
    funext j
    have hj0 : j = 0 := Fin.fin_one_eq_zero j
    subst j
    exact h1

private theorem sphereZero_left_ne_right : sphereZeroLeft ≠ sphereZeroRight := by
  intro h
  have h' := congrArg (fun p : CubeSphere 0 => p.1 (0 : Fin 1)) h
  have h01 : (0 : I) = 1 := by simpa [sphereZeroLeft, sphereZeroRight] using h'
  exact zero_ne_one h01

private instance : Finite (CubeSphere 0) := by
  apply Finite.of_surjective
    (fun b : Bool => if b then sphereZeroRight else sphereZeroLeft)
  intro p
  rcases sphereZero_eq_left_or_right p with h | h
  · exact ⟨false, by simpa [h]⟩
  · exact ⟨true, by simpa [h]⟩

private instance : DiscreteTopology (CubeSphere 0) :=
  Finite.instDiscreteTopology

/-- The operational zero-connectivity predicate is path connectedness. -/
theorem nullConnectedSpace_zero_iff_pathConnected
    {X : Type u} [TopologicalSpace X] :
    NullConnectedSpace 0 X ↔ IsPathConnected (Set.univ : Set X) := by
  classical
  constructor
  · intro hX
    let x : X := Classical.choice hX.1
    refine ⟨x, Set.mem_univ _, ?_⟩
    intro y _
    let f : C(CubeSphere 0, X) :=
      ⟨fun p => if p = sphereZeroLeft then x else y,
        continuous_of_discreteTopology⟩
    obtain ⟨z, ⟨H⟩⟩ := hX.2 0 (by omega) f
    have hleft : Path x z :=
      ⟨⟨fun t => H (t, sphereZeroLeft), by fun_prop⟩,
        by simpa [f] using H.map_zero_left sphereZeroLeft,
        by simpa using H.map_one_left sphereZeroLeft⟩
    have hright : Path y z :=
      ⟨⟨fun t => H (t, sphereZeroRight), by fun_prop⟩,
        by simpa [f, sphereZero_left_ne_right.symm] using
          H.map_zero_left sphereZeroRight,
        by simpa using H.map_one_left sphereZeroRight⟩
    exact ⟨hleft.trans hright.symm, fun _ => Set.mem_univ _⟩
  · intro hX
    obtain ⟨x, _⟩ := hX.nonempty
    refine ⟨⟨x⟩, ?_⟩
    intro j hj f
    have hj0 : j = 0 := by omega
    subst j
    let γ : ∀ p : CubeSphere 0, Path (f p) x :=
      fun p => (hX.joinedIn (x := f p) (y := x)
        (Set.mem_univ _) (Set.mem_univ _)).somePath
    refine ⟨x, ⟨{
      toContinuousMap :=
        ⟨fun tp => γ tp.2 tp.1,
          continuous_prod_of_discrete_right.mpr (fun p => map_continuous (γ p))⟩
      map_zero_left := fun p => (γ p).source'
      map_one_left := fun p => (γ p).target'
    }⟩⟩


/-- For a subset, zero-dimensional nullhomotopy connectivity agrees with
path connectedness in the ambient space. -/
theorem nullConnectedSet_zero_iff_isPathConnected
    {X : Type u} [TopologicalSpace X] (S : Set X) :
    NullConnectedSet 0 S ↔ IsPathConnected S :=
  (nullConnectedSpace_zero_iff_pathConnected (X := S)).trans
    ((pathConnectedSpace_iff_univ (X := S)).symm.trans
      (isPathConnected_iff_pathConnectedSpace (F := S)).symm)

/-- In a null-connected space, each sphere map contracts to any specified
basepoint. This is the form needed by relative homotopy arguments. -/
theorem NullConnectedSpace.homotopic_const
    {X : Type u} [TopologicalSpace X] {k j : ℕ}
    (hX : NullConnectedSpace k X) (hj : j ≤ k)
    (x₀ : X) (f : C(CubeSphere j, X)) :
    f.Homotopic (ContinuousMap.const _ x₀) := by
  obtain ⟨x, hfx⟩ := hX.2 j hj f
  have hpath : IsPathConnected (Set.univ : Set X) :=
    (nullConnectedSpace_zero_iff_pathConnected).1 (hX.mono (Nat.zero_le k))
  have hjoined : Joined x x₀ :=
    (hpath.joinedIn x (Set.mem_univ _) x₀ (Set.mem_univ _)).joined
  haveI : Nonempty (CubeSphere j) :=
    ⟨⟨fun _ => 0, ⟨0, Or.inl rfl⟩⟩⟩
  exact hfx.trans ((ContinuousMap.homotopic_const_iff).2 hjoined)

end FairDivision.Topology.NerveConnectivity
