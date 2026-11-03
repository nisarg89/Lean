import FairDivision.Topology.NerveConnectivity.PrismBoundary
import FairDivision.Topology.Volovikov.SimplexConeHomeomorph

/-!
# Filling a finite simplex prism cell

The whole prism is a simplex cell up to homeomorphism, and the natural
side-and-end boundary is its attaching boundary. Operational connectivity
therefore fills any continuous map on that boundary.
-/

set_option autoImplicit false

open scoped unitInterval Topology

namespace FairDivision.Topology.NerveConnectivity

/-- A prism on a positive-dimensional simplex is a standard simplex cell
of one higher dimension, up to homeomorphism. -/
noncomputable def finiteSimplexPrismStandardSimplexHomeomorph (j : ℕ) :
    (stdSimplex ℝ (Fin (j + 2)) × I) ≃ₜ
      stdSimplex ℝ (Fin (j + 3)) :=
  (finiteSimplexPrismCubeHomeomorph (j + 1)).trans
    (((standardSimplexCubeBodyHomeomorph (j + 2)).trans
      (finiteUnitCubeBodyHomeomorph (j + 2))).symm)

/-- The preceding whole-cell homeomorphism preserves the attaching boundary. -/
theorem finiteSimplexPrismStandardSimplex_boundary_iff (j : ℕ)
    (z : stdSimplex ℝ (Fin (j + 2)) × I) :
    ((∃ i : Fin (j + 2), z.1.1 i = 0) ∨ z.2 = 0 ∨ z.2 = 1) ↔
      ∃ i : Fin (j + 3),
        (finiteSimplexPrismStandardSimplexHomeomorph j z).1 i = 0 := by
  have hP := finiteSimplexPrismCube_boundary_iff j z
  have hS := standardSimplexCubeBody_boundary_iff (j + 1)
    (finiteSimplexPrismStandardSimplexHomeomorph j z)
  have heq :
      (((standardSimplexCubeBodyHomeomorph (j + 2)).trans
        (finiteUnitCubeBodyHomeomorph (j + 2)))
          (finiteSimplexPrismStandardSimplexHomeomorph j z)) =
      finiteSimplexPrismCubeHomeomorph (j + 1) z := by
    simp [finiteSimplexPrismStandardSimplexHomeomorph]
  rw [heq] at hS
  exact hP.trans hS.symm

/-- The natural prism boundary is the standard-simplex attaching boundary. -/
noncomputable def finiteSimplexPrismBoundaryStandardSimplexHomeomorph (j : ℕ) :
    SimplexPrismBoundary j ≃ₜ
      FairDivision.Topology.finiteStandardSimplexBoundary (j + 1) :=
  Homeomorph.subtype (finiteSimplexPrismStandardSimplexHomeomorph j)
    (finiteSimplexPrismStandardSimplex_boundary_iff j)

/-- Operational connectivity fills any map prescribed on the full boundary
of a positive-dimensional simplex prism. -/
theorem exists_finiteSimplexPrism_cellFilling
    {X : Type*} [TopologicalSpace X] {k j : ℕ}
    (hX : NullConnectedSpace k X) (hj : j + 1 ≤ k)
    (f : C(SimplexPrismBoundary j, X)) :
    ∃ F : C(stdSimplex ℝ (Fin (j + 2)) × I, X),
      F.comp (⟨Subtype.val, continuous_subtype_val⟩ :
        C(SimplexPrismBoundary j, stdSimplex ℝ (Fin (j + 2)) × I)) = f := by
  let eB := finiteSimplexPrismBoundaryStandardSimplexHomeomorph j
  let eF := finiteSimplexPrismStandardSimplexHomeomorph j
  let fStd : C(FairDivision.Topology.finiteStandardSimplexBoundary (j + 1), X) :=
    f.comp ⟨eB.symm, eB.symm.continuous⟩
  obtain ⟨FStd, hFStd⟩ :=
    FairDivision.Topology.Volovikov.exists_finiteSimplex_cellFilling hX hj fStd
  let F : C(stdSimplex ℝ (Fin (j + 2)) × I, X) :=
    FStd.comp ⟨eF, eF.continuous⟩
  refine ⟨F, ?_⟩
  apply ContinuousMap.ext
  intro b
  have hb := congrArg
    (fun q : C(FairDivision.Topology.finiteStandardSimplexBoundary (j + 1), X) =>
      q (eB b)) hFStd
  change FStd (eF b.1) = f b
  change FStd (eB b).1 = f b
  simpa [fStd, eB] using hb

end FairDivision.Topology.NerveConnectivity
