import FairDivision.Topology.Volovikov.BoundaryFilling
import FairDivision.Topology.FiniteSimplexSegment

/-!
# A finite simplex as a cone on its boundary

The forward radial map sends a boundary point and a time parameter along the
straight segment toward the barycenter. All time-one points map to the same
barycenter, so this descends continuously to the topological cone. The
remaining cell-extension step is to prove that this map is a homeomorphism.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity
open scoped unitInterval Topology

/-- The radial map from the cone on a simplex boundary to the simplex. -/
noncomputable def finiteSimplexConeMap (j : ℕ) :
    C(TopologicalCone (finiteStandardSimplexBoundary j),
      stdSimplex ℝ (Fin (j + 2))) := by
  let c : stdSimplex ℝ (Fin (j + 2)) := stdSimplex.barycenter
  let raw : C(I × finiteStandardSimplexBoundary j,
      stdSimplex ℝ (Fin (j + 2))) :=
    ⟨fun ts => finiteSimplexSegment ts.2.1 c ts.1, by
      have hbase : Continuous (fun ts : I × finiteStandardSimplexBoundary j =>
          ts.2.1) := continuous_subtype_val.comp continuous_snd
      exact finiteSimplexSegment_continuous.comp
        (continuous_fst.prodMk (hbase.prodMk continuous_const))⟩
  have hrel : ∀ a b : I × finiteStandardSimplexBoundary j,
      coneSetoid (finiteStandardSimplexBoundary j) a b → raw a = raw b := by
    intro a b hab
    rcases hab with rfl | ⟨ha, hb⟩
    · rfl
    · have ha' : raw a = c := by
        change finiteSimplexSegment a.2.1 c a.1 = c
        rw [ha]
        exact finiteSimplexSegment_one a.2.1 c
      have hb' : raw b = c := by
        change finiteSimplexSegment b.2.1 c b.1 = c
        rw [hb]
        exact finiteSimplexSegment_one b.2.1 c
      exact ha'.trans hb'.symm
  exact ⟨Quot.lift raw hrel, continuous_quot_lift hrel raw.continuous⟩

/-- The cone map restricts to the identity on the attaching boundary. -/
theorem finiteSimplexConeMap_base (j : ℕ) :
    (finiteSimplexConeMap j).comp
      (coneBase (finiteStandardSimplexBoundary j)) =
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(finiteStandardSimplexBoundary j,
            stdSimplex ℝ (Fin (j + 2)))) := by
  apply ContinuousMap.ext
  intro b
  change finiteSimplexSegment b.1
    (stdSimplex.barycenter : stdSimplex ℝ (Fin (j + 2))) (0 : I) = b.1
  exact finiteSimplexSegment_zero b.1 _

end FairDivision.Topology.Volovikov
