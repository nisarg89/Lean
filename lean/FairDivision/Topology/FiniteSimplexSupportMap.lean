import FairDivision.Topology.FiniteSimplexSupport

/-!
# Support under a finite-simplex pushforward

A positive target coordinate of a pushed-forward probability vector has a
positive source coordinate in its fiber. This elementary support fact is
shared by the BF marginal map and other realization maps.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Every positive coordinate in a simplex pushforward comes from a
positive coordinate in its source. -/
theorem finiteSimplexSupport_map_subset
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (f : V → W) (lot : stdSimplex ℝ V) :
    finiteSimplexSupport (stdSimplex.map f lot) ⊆
      (finiteSimplexSupport lot).image f := by
  classical
  intro q hq
  have hpos : 0 < (stdSimplex.map f lot).1 q :=
    (mem_finiteSimplexSupport_iff (stdSimplex.map f lot) q).mp hq
  change 0 < FunOnFinite.linearMap ℝ ℝ f lot.1 q at hpos
  rw [FunOnFinite.linearMap_apply_apply] at hpos
  obtain ⟨p, hp, hppos⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun p _ => lot.2.1 p)).mp hpos
  exact Finset.mem_image.mpr
    ⟨p, (mem_finiteSimplexSupport_iff lot p).mpr hppos,
      (Finset.mem_filter.mp hp).2⟩

end FairDivision.Topology
