import FairDivision.BF.VirtualValuationSkeleton
import FairDivision.BF.HeterogeneousOneSkeleton

/-!
# The actual manuscript virtual-valuation construction

The equal-subdivision one-skeleton exchange paths, finite closed pasting,
and actual capwise maxima on all larger faces now compose into the complete
support-local virtual-valuation specification. No virtual map, extension,
edge runner, cap regularity fact, or admissibility oracle is assumed here.
-/

set_option autoImplicit false

namespace FairDivision.BF

/-- For arbitrary bundle valuations, the manuscript's one common dummy
placeholder and every positive bundle quota admit the full continuous
support-local virtual valuation used in the heterogeneous existence proof. -/
theorem exists_virtualValuationSpec {n m q:ℕ}
    (v:Fin n→Finset (Fin m)→ℝ) (hq:1≤q):
    Nonempty (VirtualValuationSpec (q:=q) v):=by
  obtain ⟨edge,hVertex,hAdmissible⟩:=
    HeterogeneousOneSkeleton.exists_virtualValuation_oneSkeleton v hq
  apply exists_virtualValuationSpec_of_oneSkeleton v edge
  ·intro B
   have hPoint : virtualOneSkeletonVertex B = Topology.oneSkeletonVertex B := by
     classical
     apply Subtype.ext
     apply Subtype.ext
     funext C
     by_cases h : C = B
     · subst C
       simp [virtualOneSkeletonVertex, Topology.oneSkeletonVertex,
         stdSimplex.vertex_coe, Pi.single_apply]
     · simp [virtualOneSkeletonVertex, Topology.oneSkeletonVertex,
         stdSimplex.vertex_coe, Pi.single_apply, h, Ne.symm h]
   rw [hPoint]
   exact hVertex B
  ·exact hAdmissible

/-- One choice of the fully proved construction, for direct composition
with the manuscript's existing compactness/witness conversion. -/
noncomputable def virtualValuationSpec {n m q:ℕ}
    (v:Fin n→Finset (Fin m)→ℝ) (hq:1≤q):VirtualValuationSpec (q:=q) v:=
  Classical.choice (exists_virtualValuationSpec v hq)

end FairDivision.BF
