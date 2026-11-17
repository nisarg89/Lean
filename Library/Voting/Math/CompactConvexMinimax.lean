import Voting.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Shared_CompactConvexMinimax
theorem proved : Statement := by
  intro m hm f hcont hconc hconv
  let i : Fin m := ⟨0, hm⟩
  have hne : (simplex m).Nonempty := by
    refine ⟨Pi.single i 1, ?_⟩
    simpa [simplex, stdSimplex] using (single_mem_stdSimplex ℝ i)
  have hcomp : IsCompact (simplex m) := by
    simpa [simplex, stdSimplex] using (isCompact_stdSimplex ℝ (Fin m))
  have hcv : Convex ℝ (simplex m) := by
    simpa [simplex, stdSimplex] using (convex_stdSimplex ℝ (Fin m))
  have hpcont : ∀ a ∈ simplex m, ContinuousOn (fun p => f a p) (simplex m) := by
    intro a ha
    exact hcont.comp ((continuous_const.prodMk continuous_id).continuousOn) (fun p hp => ⟨ha,hp⟩)
  have hacont : ∀ p ∈ simplex m, ContinuousOn (fun a => f a p) (simplex m) := by
    intro p hp
    exact hcont.comp ((continuous_id.prodMk continuous_const).continuousOn) (fun a ha => ⟨ha,hp⟩)
  obtain ⟨p, hp, a, ha, hs⟩ := Sion.exists_isSaddlePointOn
    (f := fun p a => f a p) hne hcv hcomp
    (fun a ha => (hpcont a ha).lowerSemicontinuousOn)
    (fun a ha => (hconv a ha).quasiconvexOn)
    hcv hne hcomp
    (fun p hp => (hacont p hp).upperSemicontinuousOn)
    (fun p hp => (hconc p hp).quasiconcaveOn)
  exact ⟨a, ha, p, hp, (fun a' ha' => hs p hp a' ha'), (fun p' hp' => hs p' hp' a ha)⟩
#print axioms proved
end MetricDistortion.Contracts.Shared_CompactConvexMinimax
