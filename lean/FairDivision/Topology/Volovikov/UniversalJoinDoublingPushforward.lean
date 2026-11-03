import FairDivision.Topology.Volovikov.UniversalJoinDoublingCoordinates

/-!
# Coordinates of an injective simplex pushforward

These formulas identify weights in the two disjoint color blocks and are
used to recover the factors of a doubled universal-join point.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.Volovikov

/-- A simplex map induced by an injective vertex map preserves each source
coordinate at the corresponding image vertex. -/
theorem finiteSimplexMap_apply_injective
    {V W : Type*} [Fintype V] [Fintype W]
    (f : V → W) (hf : Function.Injective f)
    (w : stdSimplex ℝ V) (v : V) :
    (stdSimplex.map f w).1 (f v) = w.1 v := by
  classical
  change (FunOnFinite.linearMap ℝ ℝ f w.1) (f v) = w.1 v
  rw [FunOnFinite.linearMap_apply_apply]
  have hfilter : (Finset.univ.filter (fun u : V => f u = f v)) = {v} := by
    ext u
    simp [hf.eq_iff]
  rw [hfilter]
  simp

/-- A simplex map has zero weight outside the image of its vertex map. -/
theorem finiteSimplexMap_apply_not_mem_range
    {V W : Type*} [Fintype V] [Fintype W]
    (f : V → W) (w : stdSimplex ℝ V) (v : W)
    (hv : v ∉ Set.range f) :
    (stdSimplex.map f w).1 v = 0 := by
  classical
  change (FunOnFinite.linearMap ℝ ℝ f w.1) v = 0
  rw [FunOnFinite.linearMap_apply_apply]
  have hfilter : (Finset.univ.filter (fun u : V => f u = v)) = ∅ := by
    ext u
    have hne : f u ≠ v := by
      intro hu
      exact hv ⟨u, hu⟩
    simp [hne]
  rw [hfilter]
  simp

end FairDivision.Topology.Volovikov
