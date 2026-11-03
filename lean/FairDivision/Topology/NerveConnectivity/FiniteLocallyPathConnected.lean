import FairDivision.Topology.NerveConnectivity.FiniteFaceGeometry
import FairDivision.Topology.NerveConnectivity.ClosedRealization
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Separation.Hausdorff

/-!
# Local path connectedness of finite probability-simplex realizations

BF Section 4 uses local path connectedness of its finite recording graph,
and hence of the graph times an interval, when defining the signed-distance
recording function. Reuse Mathlib's path connectedness of convex sets and
preservation of local path connectedness by quotient maps. The realization
is the compact quotient of the finite disjoint union of its closed faces.
This also applies to higher-dimensional finite complexes.
-/

set_option autoImplicit false

open Set Filter Topology

namespace FairDivision.Topology.NerveConnectivity

/-- Convex subsets inherit path-connected ball neighborhoods. This is a
small subtype bridge to Mathlib's existing convex path-connectedness theorem. -/
theorem convex_locallyPathConnectedSpace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {S : Set E} (hS : Convex ℝ S) :
    LocallyPathConnectedSpace S := by
  apply LocallyPathConnectedSpace.of_bases (fun x : S=>Metric.nhds_basis_ball)
  intro x r hr
  apply IsInducing.subtypeVal.isPathConnected_iff.mpr
  have hImage : (Subtype.val : S→E) '' Metric.ball x r=S∩Metric.ball x.1 r := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.2,hz⟩
    · rintro ⟨hyS,hyBall⟩
      exact ⟨⟨y,hyS⟩,hyBall,rfl⟩
  rw [hImage]
  exact (hS.inter (convex_ball x.1 r)).isPathConnected
    ⟨x.1,x.2,Metric.mem_ball_self hr⟩

/-- Every finite standard simplex has the required local path structure,
including its lower-dimensional boundary neighborhoods. -/
theorem stdSimplex_locallyPathConnectedSpace (V : Type*) [Fintype V] :
    LocallyPathConnectedSpace (stdSimplex ℝ V) :=
  convex_locallyPathConnectedSpace (convex_stdSimplex ℝ V)

/-- Index all the nonempty faces, without selecting orientations or
subdividing the graph. -/
abbrev FiniteFaceIndex {V : Type*} (K : PreAbstractSimplicialComplex V) :=
  {F : Finset V // F∈K}

/-- The finite disjoint union of the closed faces of a finite complex. -/
abbrev FiniteFaceSource {V : Type*} [Fintype V] (K : PreAbstractSimplicialComplex V) :=
  ΣF : FiniteFaceIndex K,simplicialRealization (fullFaceComplex F.1)

/-- Forget which closed face supplied a point. On shared boundaries all
copies are sent to the same barycentric point of the realization. -/
def finiteFaceProjection {V : Type*} [Fintype V] (K : PreAbstractSimplicialComplex V) :
    FiniteFaceSource K→simplicialRealization K := fun z=>
  ⟨z.2.1,(simplicialRealization_mono (fullFaceComplex_le_of_mem K z.1.1 z.1.2)) z.2.2⟩

theorem continuous_finiteFaceProjection {V : Type*} [Fintype V]
    (K : PreAbstractSimplicialComplex V) : Continuous (finiteFaceProjection K) := by
  apply continuous_sigma
  intro F
  exact continuous_subtype_val.subtype_mk _

theorem finiteFaceProjection_surjective {V : Type*} [Fintype V]
    (K : PreAbstractSimplicialComplex V) : Function.Surjective (finiteFaceProjection K) := by
  intro x
  let F : FiniteFaceIndex K := ⟨finiteSimplexSupport x.1,x.2⟩
  let y : simplicialRealization (fullFaceComplex F.1) :=
    ⟨x.1,finiteSimplexSupport_nonempty x.1,Finset.Subset.refl _⟩
  exact ⟨⟨F,y⟩,Subtype.ext rfl⟩

/-- A finite realization is a quotient of finitely many compact standard
simplexes. This uses the existing closed-map quotient theorem. -/
theorem finiteFaceProjection_isQuotientMap {V : Type*} [Fintype V]
    (K : PreAbstractSimplicialComplex V) : IsQuotientMap (finiteFaceProjection K) := by
  classical
  letI : Fintype (FiniteFaceIndex K) := inferInstance
  letI : ∀F : FiniteFaceIndex K,CompactSpace (simplicialRealization (fullFaceComplex F.1)) :=
    fun F=>isCompact_iff_compactSpace.mp (simplicialRealization_isCompact (fullFaceComplex F.1))
  have hContinuous := continuous_finiteFaceProjection K
  exact hContinuous.isClosedMap.isQuotientMap hContinuous (finiteFaceProjection_surjective K)

/-- The topological fact used by the manuscript signed-distance recorder:
finite graph realizations, and more generally finite simplicial realizations,
are locally path connected. -/
theorem finiteRealization_locallyPathConnectedSpace {V : Type*} [Fintype V]
    (K : PreAbstractSimplicialComplex V) : LocallyPathConnectedSpace (simplicialRealization K) := by
  classical
  letI : ∀F : FiniteFaceIndex K,
      LocallyPathConnectedSpace (simplicialRealization (fullFaceComplex F.1)) := by
    intro F
    letI := stdSimplex_locallyPathConnectedSpace (FaceVertex F.1)
    exact (fullFaceRealizationHomeomorph F.1 (K.isRelLowerSet_faces F.2).1).symm.locallyPathConnectedSpace
  exact (finiteFaceProjection_isQuotientMap K).locallyPathConnectedSpace

end FairDivision.Topology.NerveConnectivity
