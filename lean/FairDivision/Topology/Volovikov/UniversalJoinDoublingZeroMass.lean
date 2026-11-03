import FairDivision.Topology.Volovikov.UniversalJoinDoublingMass
import FairDivision.Topology.Volovikov.JoinVertexSkeleton

/-!
# Zero-mass blocks and a base point for inverse join coordinates

A block with zero total probability has zero weight at every vertex. Every
point in the doubled join also witnesses a vertex of the smaller join, which
can fill the factor collapsed at an endpoint of the topological join.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

/-- Zero mass in the first color block forces every first-block weight to
vanish. -/
theorem leftDoubledJoinCoord_zero_of_mass_zero
    {m : ℕ} {G : Type*} [Fintype G]
    (w : stdSimplex ℝ (Fin (m + m) × G))
    (h : leftDoubledJoinMass w = 0) (v : Fin m × G) :
    w.1 (leftDoubledJoinVertex v) = 0 := by
  have hle : w.1 (leftDoubledJoinVertex v) ≤ leftDoubledJoinMass w := by
    unfold leftDoubledJoinMass
    exact Finset.single_le_sum
      (fun u _ => w.2.1 (leftDoubledJoinVertex u)) (Finset.mem_univ v)
  exact le_antisymm (by simpa [h] using hle) (w.2.1 _)

/-- Zero mass in the second color block forces every second-block weight to
vanish. -/
theorem rightDoubledJoinCoord_zero_of_mass_zero
    {m : ℕ} {G : Type*} [Fintype G]
    (w : stdSimplex ℝ (Fin (m + m) × G))
    (h : rightDoubledJoinMass w = 0) (v : Fin m × G) :
    w.1 (rightDoubledJoinVertex v) = 0 := by
  have hle : w.1 (rightDoubledJoinVertex v) ≤ rightDoubledJoinMass w := by
    unfold rightDoubledJoinMass
    exact Finset.single_le_sum
      (fun u _ => w.2.1 (rightDoubledJoinVertex u)) (Finset.mem_univ v)
  exact le_antisymm (by simpa [h] using hle) (w.2.1 _)

/-- Any point of the doubled finite join supplies a point of its smaller
factor, used only where that factor is collapsed by the join quotient. -/
noncomputable def doubledJoinBasepoint
    {m : ℕ} {G : Type*} [Fintype G]
    (w : simplicialRealization (universalJoinComplex (m + m) G)) :
    simplicialRealization (universalJoinComplex m G) := by
  classical
  let v := Classical.choose (FairDivision.Topology.finiteSimplexSupport_nonempty w.1)
  let i : Fin m :=
    match (finSumFinEquiv (m := m) (n := m)).symm v.1 with
    | Sum.inl j => j
    | Sum.inr j => j
  let sk := oneSkeletonVertex (i, v.2)
  exact ⟨sk.1, sk.2.1⟩

end FairDivision.Topology.Volovikov
