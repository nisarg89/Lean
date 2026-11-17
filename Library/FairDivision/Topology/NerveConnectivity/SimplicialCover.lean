import FairDivision.Topology.NerveConnectivity.Basic
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import FairDivision.Topology.FiniteSimplexSupport

/-!
# Finite simplicial subcomplex covers and their realizations

The high-dimensional nerve theorem must be stated for covers by subcomplexes.
An arbitrary family of subsets with the same intersection connectivity bounds
is not a valid replacement. This module packages the required face-level cover
condition and its finite probability-simplex realization.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- A finite family of subcomplexes that covers every nonempty face of an
ambient finite simplicial complex. Use `PreAbstractSimplicialComplex` because
an individual subcomplex need not contain every ambient vertex. -/
structure FiniteSubcomplexCover (ι : Type u) (V : Type v) [Fintype ι] where
  ambient : PreAbstractSimplicialComplex V
  pieces : ι → PreAbstractSimplicialComplex V
  piece_le : ∀ i, pieces i ≤ ambient
  covers : ∀ F : Finset V, F ∈ ambient → ∃ i, F ∈ pieces i

/-- Probability-simplex realization of a finite abstract simplicial complex. -/
def simplicialRealization {V : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V) : Set (stdSimplex ℝ V) :=
  {w | FairDivision.Topology.finiteSimplexSupport w ∈ K}

theorem simplicialRealization_mono {V : Type v} [Fintype V]
    {K L : PreAbstractSimplicialComplex V} (hKL : K ≤ L) :
    simplicialRealization K ⊆ simplicialRealization L :=
  fun _ hw => hKL hw

/-- Realizing a union of subcomplexes is the union of their realizations. -/
theorem simplicialRealization_sup {V : Type v} [Fintype V]
    (K L : PreAbstractSimplicialComplex V) :
    simplicialRealization (K ⊔ L) =
      simplicialRealization K ∪ simplicialRealization L := by
  ext w
  rfl

/-- Realizing an intersection of subcomplexes is the intersection of their
realizations. -/
theorem simplicialRealization_inf {V : Type v} [Fintype V]
    (K L : PreAbstractSimplicialComplex V) :
    simplicialRealization (K ⊓ L) =
      simplicialRealization K ∩ simplicialRealization L := by
  ext w
  rfl

/-- The realization of the ambient complex is the union of the realized
covering subcomplexes. -/
theorem FiniteSubcomplexCover.realization_eq_union
    {ι : Type u} {V : Type v} [Fintype ι] [Fintype V]
    (C : FiniteSubcomplexCover ι V) :
    simplicialRealization C.ambient =
      coverUnion (fun i => simplicialRealization (C.pieces i)) := by
  ext w
  constructor
  · intro hw
    obtain ⟨i, hi⟩ := C.covers (FairDivision.Topology.finiteSimplexSupport w) hw
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  · intro hw
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
    exact C.piece_le i hi

end FairDivision.Topology.NerveConnectivity
