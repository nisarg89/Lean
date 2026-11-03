import Mathlib.Analysis.Convex.StdSimplex

/-!
# Positive support of a finite probability simplex point

Shared by the BF auxiliary-complex realizations and the generic
simplicial-cover realization.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Vertices with strictly positive weight in a finite probability vector. -/
noncomputable def finiteSimplexSupport {V : Type*} [Fintype V]
    (w : stdSimplex ℝ V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => 0 < w.1 v)

@[simp] theorem mem_finiteSimplexSupport_iff {V : Type*} [Fintype V]
    (w : stdSimplex ℝ V) (v : V) :
    v ∈ finiteSimplexSupport w ↔ 0 < w.1 v := by
  classical
  simp [finiteSimplexSupport]

/-- A deterministic simplex point is supported on its unique vertex. -/
theorem finiteSimplexSupport_vertex {V : Type*} [Fintype V]
    [DecidableEq V] (v : V) :
    finiteSimplexSupport (stdSimplex.vertex (S := ℝ) v) = {v} := by
  ext u
  simp only [finiteSimplexSupport, Finset.mem_filter,
    Finset.mem_univ, true_and, stdSimplex.vertex_coe,
    Pi.single_apply, Finset.mem_singleton]
  split_ifs <;> simp_all

/-- A probability vector has at least one strictly positive coordinate. -/
theorem finiteSimplexSupport_nonempty {V : Type*} [Fintype V]
    (w : stdSimplex ℝ V) : (finiteSimplexSupport w).Nonempty := by
  classical
  by_contra h
  have hzero : ∀ v : V, w.1 v = 0 := by
    intro v
    have hnot : ¬ 0 < w.1 v := by
      intro hpos
      apply h
      exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩⟩
    exact le_antisymm (le_of_not_gt hnot) (w.2.1 v)
  have hsum := w.2.2
  simp [hzero] at hsum

end FairDivision.Topology
