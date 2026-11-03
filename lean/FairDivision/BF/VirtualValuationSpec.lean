import FairDivision.BF.HeterogeneousAdmissibility
import FairDivision.Topology.UnlabeledMarginalFin

/-!
# BF Section 5 virtual-valuation construction target

This records the exact interface that the manuscript's facewise construction
must produce. A point is a lottery on `(q-1)`-item bundles with one common
dummy placeholder. `stock` is the union of its positively supported bundles,
so the admissibility field asserts precisely the support-local witness and
shortening guarantees, not an unrestricted global guarantee.

The structure is an intermediate specification. The certificate will construct
an inhabitant from arbitrary valuations before using it in the final theorem.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision.Topology

/-- The union of all bundles appearing with positive probability. -/
noncomputable def finMarginalStock {m r : ℕ}
    (x : stdSimplex ℝ (FixedFinMarginalBundle m r)) :
    Finset (Fin (m + 1)) := by
  classical
  exact (finiteSimplexSupport x).biUnion (fun B => B.1)

/-- At a deterministic lottery, the support union is exactly its bundle. -/
theorem finMarginalStock_vertex {m r : ℕ}
    (B : FixedFinMarginalBundle m r) :
    finMarginalStock (stdSimplex.vertex B) = B.1 := by
  classical
  simp [finMarginalStock, finiteSimplexSupport_vertex]

/-- The manuscript's vertex score has the required support-local witnesses. -/
theorem virtualVertex_admissible {n m q : ℕ}
    (v : Fin n → Finset (Fin m) → ℝ)
    (B : FixedFinMarginalBundle m (q - 1)) (hq : 1 ≤ q) :
    IsAdmissible q 0
      (fun i S => v i (marginalRealPart S))
      (finMarginalStock (stdSimplex.vertex B))
      (fun i => v i (marginalRealPart B.1)) := by
  rw [finMarginalStock_vertex]
  exact isAdmissible_vertex
    (fun i S => v i (marginalRealPart S)) B.1 B.1
    hq B.2 Finset.Subset.rfl

/-- Every positively supported bundle is contained in the support union. -/
theorem supportedBundle_subset_finMarginalStock {m r : ℕ}
    (x : stdSimplex ℝ (FixedFinMarginalBundle m r))
    (B : FixedFinMarginalBundle m r)
    (hB : B ∈ finiteSimplexSupport x) :
    B.1 ⊆ finMarginalStock x := by
  classical
  intro g hg
  exact Finset.mem_biUnion.mpr ⟨B, hB, hg⟩

/-- Every item in a marginal support union occurs in the bundle of a
positive-weight source auxiliary vertex. -/
theorem exists_source_of_finMarginalStock_mem
    {k m r : ℕ} {D : Finset (Fin m)}
    (x : unlabeledLotterySpace k m r 1 D) (i : Fin k)
    (g : Fin (m + 1))
    (hg : g ∈ finMarginalStock (unlabeledFinMarginal i x)) :
    ∃ p ∈ unlabeledLotterySupport x.1,
      g ∈ (finMarginalVertex (canonicalMarginalVertex p i)).1 := by
  classical
  obtain ⟨B, hB, hgB⟩ := Finset.mem_biUnion.mp hg
  obtain ⟨p, hp, hpB⟩ :=
    exists_source_of_finMarginal_support x i B hB
  refine ⟨p, hp, ?_⟩
  rw [hpB]
  exact hgB

/-- Required output of the manuscript's virtual-valuation construction.
The finite-coordinate dummy is zero, and `marginalRealPart` removes it. -/
structure VirtualValuationSpec {n m q : ℕ}
    (v : Fin n → Finset (Fin m) → ℝ) where
  score : stdSimplex ℝ (FixedFinMarginalBundle m (q - 1)) →
    Fin n → ℝ
  continuous_score : Continuous score
  vertex_score : ∀ F : FixedFinMarginalBundle m (q - 1),
    score (stdSimplex.vertex F) =
      fun i => v i (marginalRealPart F.1)
  admissible_score : ∀ x,
    IsAdmissible q 0
      (fun i S => v i (marginalRealPart S))
      (finMarginalStock x) (score x)

end FairDivision.BF
