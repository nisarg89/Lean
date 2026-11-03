import FairDivision.Topology.NerveConnectivity.SimplicialCover

/-!
# Closedness of finite simplicial realizations

The closed-set property is one of the geometric inputs to the positive-dimensional
binary gluing theorem. A realization is a finite union of closed coordinate faces.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u

/-- A coordinate face of the probability simplex: all vertices outside `F`
have zero weight. -/
def coordinateFace {V : Type u} [Fintype V] (F : Finset V) :
    Set (stdSimplex ℝ V) :=
  {w | ∀ v : V, v ∉ F → w.1 v = 0}

theorem coordinateFace_isClosed {V : Type u} [Fintype V]
    (F : Finset V) : IsClosed (coordinateFace F) := by
  have heq : coordinateFace F =
      ⋂ v : {v : V // v ∉ F}, {w : stdSimplex ℝ V | w.1 v.1 = 0} := by
    ext w
    simp only [coordinateFace, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h v
      exact h v.1 v.2
    · intro h v hv
      exact h ⟨v, hv⟩
  rw [heq]
  apply isClosed_iInter
  intro v
  exact isClosed_eq ((continuous_apply v.1).comp continuous_subtype_val)
    continuous_const

/-- A finite-vertex simplicial realization is the union of its closed
coordinate faces. -/
theorem simplicialRealization_eq_coordinateFaces
    {V : Type u} [Fintype V] (K : PreAbstractSimplicialComplex V) :
    simplicialRealization K =
      ⋃ F ∈ K.faces, coordinateFace F := by
  classical
  ext w
  constructor
  · intro hw
    refine Set.mem_iUnion.mpr ⟨FairDivision.Topology.finiteSimplexSupport w,
      Set.mem_iUnion.mpr ⟨hw, ?_⟩⟩
    intro v hv
    have hnot : ¬ 0 < w.1 v := by
      intro hpos
      exact hv ((FairDivision.Topology.mem_finiteSimplexSupport_iff w v).2 hpos)
    exact le_antisymm (le_of_not_gt hnot) (w.2.1 v)
  · intro hw
    obtain ⟨F, hF, hface⟩ := Set.mem_iUnion₂.mp hw
    have hsubset : FairDivision.Topology.finiteSimplexSupport w ⊆ F := by
      intro v hv
      by_contra hnot
      have hzero := hface v hnot
      have hpos := (FairDivision.Topology.mem_finiteSimplexSupport_iff w v).1 hv
      exact (ne_of_gt hpos) hzero
    exact (K.isRelLowerSet_faces hF).2 hsubset
      (FairDivision.Topology.finiteSimplexSupport_nonempty w)

/-- Every finite simplicial subcomplex is a closed subset of the finite
probability simplex. -/
theorem simplicialRealization_isClosed
    {V : Type u} [Fintype V] (K : PreAbstractSimplicialComplex V) :
    IsClosed (simplicialRealization K) := by
  rw [simplicialRealization_eq_coordinateFaces]
  exact (Set.toFinite K.faces).isClosed_biUnion
    (fun F _ => coordinateFace_isClosed F)


/-- A finite-vertex simplicial realization is compact. -/
theorem simplicialRealization_isCompact
    {V : Type u} [Fintype V] (K : PreAbstractSimplicialComplex V) :
    IsCompact (simplicialRealization K) :=
  (simplicialRealization_isClosed K).isCompact

/-- Every member of a finite simplicial cover is closed in the ambient
probability simplex. -/
theorem FiniteSubcomplexCover.piece_isClosed
    {ι : Type*} {V : Type u} [Fintype ι] [Fintype V]
    (C : FiniteSubcomplexCover ι V) (i : ι) :
    IsClosed (simplicialRealization (C.pieces i)) :=
  simplicialRealization_isClosed (C.pieces i)

/-- Every intersection in a finite simplicial cover is closed. -/
theorem FiniteSubcomplexCover.intersection_isClosed
    {ι : Type*} {V : Type u} [Fintype ι] [Fintype V]
    (C : FiniteSubcomplexCover ι V) (J : Finset ι) :
    IsClosed (coverIntersection
      (fun i => simplicialRealization (C.pieces i)) J) := by
  unfold coverIntersection
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro _
  exact C.piece_isClosed i

end FairDivision.Topology.NerveConnectivity
