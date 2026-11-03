import FairDivision.Topology.VariableDummyStockRealization

/-!
# An active vertex from a nonempty restricted realization

A nonempty auxiliary realization contains a positive-weight vertex. Its real
bundles obey the real-stock restriction. The induction uses this vertex to
totalize the maps in the two reduction homeomorphisms.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open NerveConnectivity

/-- Extract a stock-respecting auxiliary vertex from a nonempty realization. -/
theorem exists_variableStockVertex_of_nonempty {k m : ℕ}
    {D E : Finset (Fin m)} {r c : Fin k → ℕ}
    (h : Nonempty (simplicialRealization (variableStockComplex D E r c))) :
    ∃ p : VariableUnlabeledVertex k m D r c,
      ∀ i : Fin k, (p.1 i).1 ⊆ E := by
  obtain ⟨⟨lot, hlot⟩⟩ := h
  obtain ⟨p, hp⟩ := finiteSimplexSupport_nonempty lot
  exact ⟨p, hlot.2 p hp⟩

end FairDivision.Topology
