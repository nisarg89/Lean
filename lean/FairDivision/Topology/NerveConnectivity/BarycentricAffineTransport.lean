import FairDivision.Topology.NerveConnectivity.FiniteSimplexAffinePoint
import FairDivision.Topology.NerveConnectivity.BarycentricRealizationMap
import FairDivision.Topology.NerveConnectivity.BarycentricMeshStep

/-!
# Affine evaluation commutes with barycentric subdivision

The forward subdivision homeomorphism is affine on each barycentric
simplex. Evaluating it in any real normed vector space agrees with
weighted evaluation at the face centroids.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u v

private theorem faceBaryWeight_smul_sum_eq_centroid
    {V : Type u} {E : Type v} [Fintype V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Finset V) (p : V → E) (hF : F.Nonempty) :
    (∑ i : V, faceBaryWeight F i • p i) = F.centroid ℝ p := by
  classical
  rw [finiteCentroid_eq_inv_card_smul_sum F p hF]
  simp [faceBaryWeight, Finset.sum_ite, Finset.smul_sum]

/-- Affine evaluation commutes with the canonical subdivision forward map. -/
theorem finiteSimplexAffinePoint_barycentricForward
    {V : Type u} {E : Type v} [Fintype V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : PreAbstractSimplicialComplex V) (p : V → E)
    (z : simplicialRealization (barycentricSubdivision K)) :
    finiteSimplexAffinePoint p (barycentricForwardSimplex z) =
      finiteSimplexAffinePoint (fun F : Finset V => F.centroid ℝ p) z.1 := by
  classical
  have hinner : ∀ F : Finset V,
      z.1.1 F • (∑ i : V, faceBaryWeight F i • p i) =
        z.1.1 F • F.centroid ℝ p := by
    intro F
    by_cases hF : F.Nonempty
    · rw [faceBaryWeight_smul_sum_eq_centroid F p hF]
    · have hzero : z.1.1 F = 0 := by
        have hnot : F ∉ FairDivision.Topology.finiteSimplexSupport z.1 := by
          intro hFC
          exact hF ((K.isRelLowerSet_faces (z.2.2.1 F hFC)).1)
        have hnotpos : ¬ 0 < z.1.1 F :=
          fun hp => hnot ((FairDivision.Topology.mem_finiteSimplexSupport_iff z.1 F).2 hp)
        exact le_antisymm (le_of_not_gt hnotpos) (z.1.2.1 F)
      simp [hzero]
  calc
    finiteSimplexAffinePoint p (barycentricForwardSimplex z) =
        ∑ i : V, ∑ F : Finset V,
          (z.1.1 F * faceBaryWeight F i) • p i := by
      simp [finiteSimplexAffinePoint, barycentricForwardSimplex,
        barycentricForwardWeight, Finset.sum_smul]
    _ = ∑ F : Finset V,
          z.1.1 F • (∑ i : V, faceBaryWeight F i • p i) := by
      rw [Finset.sum_comm]
      congr 1
      ext F
      rw [Finset.smul_sum]
      congr 1
      ext i
      rw [smul_smul]
    _ = ∑ F : Finset V, z.1.1 F • F.centroid ℝ p := by
      apply Finset.sum_congr rfl
      intro F _
      exact hinner F
    _ = finiteSimplexAffinePoint (fun F : Finset V => F.centroid ℝ p) z.1 := rfl

end FairDivision.Topology.NerveConnectivity
