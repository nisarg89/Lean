import FairDivision.BF.HeterogeneousExchangeChain
import FairDivision.BF.VirtualValuationSpec
import FairDivision.Topology.SimplexOneSkeletonMap

/-!
# Manuscript Section 5 virtual valuations on the lottery one-skeleton

For each edge, fix its finite one-item exchange sequence once. Run that
sequence on equal subintervals; within an exchange, use the literal half- or
quarter-subdivision score path from the manuscript. These are vector-valued
paths, so every agent uses the same subdivisions. The original local witness
and shortening proofs certify every path value inside its endpoint pool.

The generic finite closed-face pasting lemma then supplies an actual
continuous map on lotteries with support of cardinality at most two. At an
edge's endpoints the vertex score is retained, while at every other point its
witnesses use only the actual support pool. This is the base for the paper's
higher-face coordinatewise cap-maximum construction.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.HeterogeneousOneSkeleton

open FairDivision.Topology

/-- The exact common one-skeleton map required before the higher-dimensional
face extension. Its stock is the ACTUAL lottery support union at every point. -/
theorem exists_virtualValuation_oneSkeleton
    {n m q : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hq : 1 ≤ q) :
    ∃ score : C(SmallSupportSimplex (FixedFinMarginalBundle m (q - 1)) 2,
        Fin n → ℝ),
      (∀ F : FixedFinMarginalBundle m (q - 1),
        score (oneSkeletonVertex F) = fun i => v i (marginalRealPart F.1)) ∧
      ∀ x, IsAdmissible q 0
        (fun i S => v i (marginalRealPart S))
        (finMarginalStock x.1) (score x) := by
  classical
  let value : FixedFinMarginalBundle m (q - 1) → Fin n → ℝ :=
    fun F i => v i (marginalRealPart F.1)
  let extended : Fin n → Finset (Fin (m + 1)) → ℝ :=
    fun i S => v i (marginalRealPart S)
  have paths : ∀ F G : FixedFinMarginalBundle m (q - 1),
      ∃ γ : Path (value F) (value G),
        ∀ t, IsAdmissible q 0 extended (F.1 ∪ G.1) (γ t) := by
    intro F G
    exact exists_admissible_bundle_path 0 extended (F.1 ∪ G.1) F.1 G.1
      hq F.2 G.2 Finset.subset_union_left Finset.subset_union_right
  choose edge edge_admissible using paths
  obtain ⟨score, hvertex, hface⟩ :=
    exists_simplexOneSkeletonMap_with_vertices value edge
  refine ⟨score, hvertex, ?_⟩
  intro x
  let S : SimplexSmallFace (FixedFinMarginalBundle m (q - 1)) :=
    ⟨finiteSimplexSupport x.1, finiteSimplexSupport_nonempty x.1, x.2⟩
  have hx : x.1 ∈ simplexSupportFace S.1 := Finset.Subset.rfl
  rw [hface S x hx]
  let F := (smallFaceEndpoints S).first
  let G := (smallFaceEndpoints S).second
  have hF : F ∈ finiteSimplexSupport x.1 := by
    change F ∈ S.1
    rw [(smallFaceEndpoints S).face_eq]
    simp [F]
  have hG : G ∈ finiteSimplexSupport x.1 := by
    change G ∈ S.1
    rw [(smallFaceEndpoints S).face_eq]
    simp [G]
  have hpool : F.1 ∪ G.1 ⊆ finMarginalStock x.1 :=
    Finset.union_subset
      (supportedBundle_subset_finMarginalStock x.1 F hF)
      (supportedBundle_subset_finMarginalStock x.1 G hG)
  exact isAdmissible_mono hpool (edge_admissible F G _)

end FairDivision.BF.HeterogeneousOneSkeleton
