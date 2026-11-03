import FairDivision.Topology.FiniteSimplexCubeBoundary

/-!
# BF names for the shared simplex-cube body homeomorphisms

The geometric proofs are in `FiniteSimplexCubeBody`, which is independent of
BF connectivity. These aliases preserve the original BF prism API.
-/

set_option autoImplicit false

open scoped unitInterval Topology

namespace FairDivision.Topology.NerveConnectivity

noncomputable abbrev finiteSimplexCubeAmbientHomeomorph (n : ℕ) :
    (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
  FairDivision.Topology.finiteSimplexCubeAmbientHomeomorph n

theorem finiteSimplexCubeAmbient_image (n : ℕ) :
    finiteSimplexCubeAmbientHomeomorph n ''
      FairDivision.Topology.finiteSimplexPolytope n =
        FairDivision.Topology.finiteUnitCube n :=
  FairDivision.Topology.finiteSimplexCubeAmbient_image n

noncomputable abbrev finiteSimplexCubeBodyHomeomorph (n : ℕ) :
    FairDivision.Topology.finiteSimplexPolytope n ≃ₜ
      FairDivision.Topology.finiteUnitCube n :=
  FairDivision.Topology.finiteSimplexCubeBodyHomeomorph n

noncomputable abbrev standardSimplexCubeBodyHomeomorph (n : ℕ) :
    stdSimplex ℝ (Fin (n + 1)) ≃ₜ FairDivision.Topology.finiteUnitCube n :=
  FairDivision.Topology.standardSimplexCubeBodyHomeomorph n

noncomputable abbrev finiteUnitCubeBodyHomeomorph (n : ℕ) :
    FairDivision.Topology.finiteUnitCube n ≃ₜ I^ (Fin n) :=
  FairDivision.Topology.finiteUnitCubeBodyHomeomorph n

end FairDivision.Topology.NerveConnectivity
