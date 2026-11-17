import FairDivision.Topology.NerveConnectivity.PrismCubeCoordinates

/-!
# Boundary of a finite simplex prism

The side boundary of a simplex prism and its two time ends correspond
exactly to the boundary of the cube under the whole-body homeomorphism.
The indexing starts with a positive-dimensional simplex, which is the
cell case needed by the higher-dimensional homotopy extension.
-/

set_option autoImplicit false

open scoped unitInterval Topology

namespace FairDivision.Topology.NerveConnectivity

open Set

/-- The ordinary boundary of a positive-dimensional simplex prism. -/
abbrev SimplexPrismBoundary (j : ℕ) :=
  {z : stdSimplex ℝ (Fin (j + 2)) × I //
    (∃ i : Fin (j + 2), z.1.1 i = 0) ∨ z.2 = 0 ∨ z.2 = 1}

private theorem finiteCubeSnoc_boundary_iff (n : ℕ)
    (p : I^ (Fin n)) (t : I) :
    Fin.snoc p t ∈ Cube.boundary (Fin (n + 1)) ↔
      p ∈ Cube.boundary (Fin n) ∨ t = 0 ∨ t = 1 := by
  constructor
  · rintro ⟨i, hi⟩
    cases i using Fin.lastCases with
    | last =>
        right
        simpa only [Fin.snoc_last] using hi
    | cast i =>
        left
        exact ⟨i, by simpa only [Fin.snoc_castSucc] using hi⟩
  · rintro (⟨i, hi⟩ | h0 | h1)
    · exact ⟨Fin.castSucc i, by simpa only [Fin.snoc_castSucc] using hi⟩
    · exact ⟨Fin.last n, by simpa only [Fin.snoc_last] using Or.inl h0⟩
    · exact ⟨Fin.last n, by simpa only [Fin.snoc_last] using Or.inr h1⟩

private theorem finiteSimplexCubeAmbient_frontier_iff (n : ℕ)
    (x : FairDivision.Topology.finiteSimplexPolytope n) :
    x.1 ∈ frontier (FairDivision.Topology.finiteSimplexPolytope n) ↔
      (finiteSimplexCubeBodyHomeomorph n x).1 ∈
        frontier (FairDivision.Topology.finiteUnitCube n) := by
  let e := finiteSimplexCubeAmbientHomeomorph n
  have hfrontier := (Classical.choose_spec (exists_homeomorph_image_eq
    (FairDivision.Topology.finiteSimplexPolytope_convex n)
    (FairDivision.Topology.finiteSimplexPolytope_interior_nonempty n)
    (NormedSpace.isVonNBounded_of_isBounded _
      (FairDivision.Topology.finiteSimplexPolytope_isBounded n))
    (FairDivision.Topology.finiteUnitCube_convex n)
    (FairDivision.Topology.finiteUnitCube_interior_nonempty n)
    (NormedSpace.isVonNBounded_of_isBounded _
      (FairDivision.Topology.finiteUnitCube_isBounded n)))).2.2
  change x.1 ∈ frontier (FairDivision.Topology.finiteSimplexPolytope n) ↔
    e x.1 ∈ frontier (FairDivision.Topology.finiteUnitCube n)
  constructor
  · intro hx
    rw [← hfrontier]
    exact ⟨x.1, hx, rfl⟩
  · intro hx
    rw [← hfrontier] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact e.injective hxy ▸ hy

private theorem finiteUnitCubeBody_boundary_iff (n : ℕ)
    (x : FairDivision.Topology.finiteUnitCube n) :
    (finiteUnitCubeBodyHomeomorph n x) ∈ Cube.boundary (Fin n) ↔
      x.1 ∈ frontier (FairDivision.Topology.finiteUnitCube n) := by
  rw [FairDivision.Topology.mem_frontier_finiteUnitCube_iff]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨x.2, i, ?_⟩
    rcases hi with h0 | h1
    · exact Or.inl (by simpa [finiteUnitCubeBodyHomeomorph, FairDivision.Topology.finiteUnitCubeBodyHomeomorph] using congrArg Subtype.val h0)
    · exact Or.inr (by simpa [finiteUnitCubeBodyHomeomorph, FairDivision.Topology.finiteUnitCubeBodyHomeomorph] using congrArg Subtype.val h1)
  · rintro ⟨_, i, hi⟩
    refine ⟨i, ?_⟩
    rcases hi with h0 | h1
    · exact Or.inl (Subtype.ext h0)
    · exact Or.inr (Subtype.ext h1)

/-- The simplex side boundary corresponds to the boundary of its cube body. -/
theorem standardSimplexCubeBody_boundary_iff (j : ℕ)
    (x : stdSimplex ℝ (Fin (j + 2))) :
    (∃ i : Fin (j + 2), x.1 i = 0) ↔
      (((standardSimplexCubeBodyHomeomorph (j + 1)).trans
        (finiteUnitCubeBodyHomeomorph (j + 1))) x) ∈
          Cube.boundary (Fin (j + 1)) := by
  change (∃ i : Fin (j + 2), x.1 i = 0) ↔
    (finiteUnitCubeBodyHomeomorph (j + 1)
      (standardSimplexCubeBodyHomeomorph (j + 1) x)) ∈ Cube.boundary (Fin (j + 1))
  rw [finiteUnitCubeBody_boundary_iff]
  exact (FairDivision.Topology.finiteStandardSimplex_boundary_iff_frontier j x).trans
    (finiteSimplexCubeAmbient_frontier_iff (j + 1)
      (FairDivision.Topology.stdSimplexPolytopeHomeomorph (j + 1) x))

/-- The natural boundary of a simplex prism is the preimage of the cube boundary. -/
theorem finiteSimplexPrismCube_boundary_iff (j : ℕ)
    (z : stdSimplex ℝ (Fin (j + 2)) × I) :
    ((∃ i : Fin (j + 2), z.1.1 i = 0) ∨ z.2 = 0 ∨ z.2 = 1) ↔
      finiteSimplexPrismCubeHomeomorph (j + 1) z ∈
        Cube.boundary (Fin (j + 2)) := by
  change _ ↔ Fin.snoc
    (((standardSimplexCubeBodyHomeomorph (j + 1)).trans
      (finiteUnitCubeBodyHomeomorph (j + 1))) z.1) z.2 ∈
      Cube.boundary (Fin (j + 2))
  rw [finiteCubeSnoc_boundary_iff]
  exact or_congr (standardSimplexCubeBody_boundary_iff j z.1) Iff.rfl

/-- The boundary of a finite simplex prism is the operational cube sphere. -/
noncomputable def finiteSimplexPrismBoundaryCubeSphereHomeomorph (j : ℕ) :
    SimplexPrismBoundary j ≃ₜ CubeSphere (j + 1) :=
  Homeomorph.subtype (finiteSimplexPrismCubeHomeomorph (j + 1))
    (finiteSimplexPrismCube_boundary_iff j)

end FairDivision.Topology.NerveConnectivity
