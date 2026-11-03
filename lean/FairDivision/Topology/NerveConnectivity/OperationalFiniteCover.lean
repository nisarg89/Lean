import FairDivision.Topology.NerveConnectivity.OperationalOpenCoverGluing

/-!
# Unconditional finite-subcomplex cover connectivity

This is the public operational form of the finite-cover connectivity
result needed by the corrected BF auxiliary-complex induction. The
positive-dimensional binary step is supplied by finite-cone gluing;
the degree-zero step is the compiled path-connected union theorem.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- A finite subcomplex cover satisfying the nerve-style intersection
connectivity bounds has a connected union through degree `k`. -/
theorem operationalFiniteCover
    {V : Type v} [Fintype V] (k : ℕ) :
    ∀ {ι : Type u} [Fintype ι] [Nonempty ι]
      (C : ι → PreAbstractSimplicialComplex V),
      OperationalNerveHypotheses k C →
      NullConnectedSet k (simplicialRealization (⨆ i, C i)) :=
  operationalFiniteCover_of_binaryGluing
    operationalBinaryGluing_of_openCover k

end FairDivision.Topology.NerveConnectivity
