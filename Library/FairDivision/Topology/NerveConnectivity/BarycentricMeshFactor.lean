import FairDivision.Topology.NerveConnectivity.BarycentricMeshStep
import FairDivision.Topology.NerveConnectivity.BarycentricSubdivision

/-!
# Uniform one-step barycentric mesh contraction

Nested nonempty faces inside a parent face of at most `N` vertices have
centroids at distance at most `(N-1)/N` times the parent vertex bound.
The result is independent of a particular embedding of the complex.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- A uniform cardinal bound turns the exact nested-centroid inequality
into a strict contraction factor. -/
theorem card_mul_dist_centroid_le_meshFactor
    {ι : Type u} {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s t : Finset ι) (p : ι → E) (δ : ℝ) (N : ℕ)
    (hs : s.Nonempty) (hst : s ⊆ t)
    (hN : t.card ≤ N) (hδ : 0 ≤ δ)
    (hpair : ∀ i ∈ t, ∀ j ∈ t, dist (p i) (p j) ≤ δ) :
    (N : ℝ) * dist (t.centroid ℝ p) (s.centroid ℝ p) ≤
      ((N : ℝ) - 1) * δ := by
  classical
  have ht : t.Nonempty := hs.mono hst
  have hmpos : (0 : ℝ) < t.card := by
    exact_mod_cast Finset.card_pos.mpr ht
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast lt_of_lt_of_le (Finset.card_pos.mpr ht) hN
  have hNnonneg : (0 : ℝ) ≤ N := le_of_lt hNpos
  have hr : (1 : ℝ) ≤ s.card := by
    exact_mod_cast Finset.one_le_card.mpr hs
  have hmN : (t.card : ℝ) ≤ N := by exact_mod_cast hN
  have hcardNat : t.card = s.card + (t \ s).card := by
    have h := Finset.card_sdiff_add_card_eq_card hst
    omega
  have hcard : (t.card : ℝ) = (s.card : ℝ) + ((t \ s).card : ℝ) := by
    exact_mod_cast hcardNat
  have hcross : ((t \ s).card : ℝ) * N ≤
      ((N : ℝ) - 1) * t.card := by
    have hmul := mul_le_mul_of_nonneg_right hr hNnonneg
    nlinarith
  have hbase := card_mul_dist_centroid_le s t p δ hs hst hpair
  have hscaled := mul_le_mul_of_nonneg_left hbase hNnonneg
  have hscaled' := mul_le_mul_of_nonneg_right hcross hδ
  have hbound : (t.card : ℝ) *
      ((N : ℝ) * dist (t.centroid ℝ p) (s.centroid ℝ p)) ≤
      (t.card : ℝ) * (((N : ℝ) - 1) * δ) := by
    nlinarith
  exact (mul_le_mul_iff_of_pos_left hmpos).mp hbound

/-- Every simplex in the barycentric subdivision inherits the same strict
vertex-distance factor from the largest original face in its chain. -/
theorem barycentricSubdivision_vertexMeshFactor
    {V : Type u} {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : PreAbstractSimplicialComplex V)
    (p : V → E) (δ : ℝ) (N : ℕ)
    (hδ : 0 ≤ δ)
    (hsize : ∀ F : Finset V, F ∈ K → F.card ≤ N)
    (hmesh : ∀ F : Finset V, F ∈ K →
      ∀ i ∈ F, ∀ j ∈ F, dist (p i) (p j) ≤ δ)
    (C : Finset (Finset V)) (hC : C ∈ barycentricSubdivision K)
    (F G : Finset V) (hF : F ∈ C) (hG : G ∈ C) :
    (N : ℝ) * dist (F.centroid ℝ p) (G.centroid ℝ p) ≤
      ((N : ℝ) - 1) * δ := by
  classical
  obtain ⟨M, hM, htop⟩ := finiteChain_exists_greatest C hC.1 hC.2.2
  have hMK : M ∈ K := hC.2.1 M hM
  have hMN : M.card ≤ N := hsize M hMK
  rcases hC.2.2.total hF hG with hFG | hGF
  · have hGN : G.card ≤ N :=
      (Finset.card_le_card (htop G hG)).trans hMN
    have hpair : ∀ i ∈ G, ∀ j ∈ G, dist (p i) (p j) ≤ δ := by
      intro i hi j hj
      exact hmesh M hMK i (htop G hG hi) j (htop G hG hj)
    have h := card_mul_dist_centroid_le_meshFactor F G p δ N
      (K.isRelLowerSet_faces (hC.2.1 F hF)).1 hFG hGN hδ hpair
    simpa only [dist_comm] using h
  · have hFN : F.card ≤ N :=
      (Finset.card_le_card (htop F hF)).trans hMN
    have hpair : ∀ i ∈ F, ∀ j ∈ F, dist (p i) (p j) ≤ δ := by
      intro i hi j hj
      exact hmesh M hMK i (htop F hF hi) j (htop F hF hj)
    exact card_mul_dist_centroid_le_meshFactor G F p δ N
      (K.isRelLowerSet_faces (hC.2.1 G hG)).1 hGF hFN hδ hpair

end FairDivision.Topology.NerveConnectivity
