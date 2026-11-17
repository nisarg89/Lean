import FairDivision.Topology.SphericalCapBasic
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Upper hemicontinuity of chordal spherical caps

This is the closed-graph half of the moving-cap argument.  Its proof is
valid for any compact sphere and does not use inner-product geometry.
-/

set_option autoImplicit false

namespace FairDivision.Topology

private theorem upperHemicontinuous_of_closed_graph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace Y]
    (K : X → Set Y)
    (hGraph : IsClosed {p : X × Y | p.2 ∈ K p.1}) :
    UpperHemicontinuous K := by
  rw [upperHemicontinuous_iff_isClosed_compl_preimage_Iic_compl]
  intro C hC
  have hClosed : IsClosed {p : X × Y | p.2 ∈ K p.1 ∧ p.2 ∈ C} := by
    exact hGraph.inter (hC.preimage continuous_snd)
  have hImage : IsClosed (Prod.fst '' {p : X × Y | p.2 ∈ K p.1 ∧ p.2 ∈ C}) :=
    isClosedMap_fst_of_compactSpace _ hClosed
  convert hImage using 1
  ext x
  simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_Iic,
    Set.mem_compl_iff, Set.subset_def, Set.mem_image, Set.mem_setOf_eq]
  aesop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem sphericalCap_graph_isClosed :
    IsClosed {p : ClosedUnitBall E × UnitSphere E | p.2 ∈ sphericalCap p.1} := by
  change IsClosed {p : ClosedUnitBall E × UnitSphere E |
    dist (p.1 : E) (p.2 : E) ≤ 2 * (1 - ‖(p.1 : E)‖)}
  exact isClosed_le (by fun_prop) (by fun_prop)

theorem sphericalCap_upperHemicontinuous :
    UpperHemicontinuous (sphericalCap (E := E)) :=
  upperHemicontinuous_of_closed_graph (sphericalCap (E := E))
    sphericalCap_graph_isClosed

end FairDivision.Topology
