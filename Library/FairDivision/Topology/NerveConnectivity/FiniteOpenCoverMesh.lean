import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Subordinating small sets to an open cover

A compact metric source has a uniform Lebesgue number for any open cover.
Every nonempty subset of the source with smaller pairwise diameter lies
inside one cover member. This form is convenient for geometric simplices.
-/

set_option autoImplicit false

open Metric

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- Uniform diameter threshold for subordinating nonempty subsets of a
compact metric source to an open cover. -/
theorem exists_smallSet_subordinate_to_openCover
    {X : Type u} {ι : Type v} [PseudoMetricSpace X]
    (s : Set X) (hs : IsCompact s)
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : s ⊆ ⋃ i, U i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : Set X,
      t.Nonempty → t ⊆ s →
      (∀ x ∈ t, ∀ y ∈ t, dist x y < δ) →
      ∃ i, t ⊆ U i := by
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric hs hU hcover
  refine ⟨δ, hδ, ?_⟩
  intro t htn hts hsmall
  obtain ⟨x, hx⟩ := htn
  obtain ⟨i, hi⟩ := hball x (hts hx)
  refine ⟨i, ?_⟩
  intro y hy
  exact hi (mem_ball.mpr (by simpa only [dist_comm] using hsmall x hx y hy))

end FairDivision.Topology.NerveConnectivity
