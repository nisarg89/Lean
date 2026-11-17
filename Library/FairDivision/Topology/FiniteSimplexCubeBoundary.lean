import FairDivision.Topology.FiniteSimplexCubeBody
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Homeomorph.Lemmas
import FairDivision.Topology.NerveConnectivity.NullHomotopy

/-!
# The boundary of a finite simplex and a cube

For the equivariant cellular transfer, an attaching face of a finite
simplicial realization has to be compared with the cube-boundary sphere
used by `NerveConnectivity.NullConnectedSpace`. Mathlib's convex gauge
rescaling provides the geometric core: the frontiers of two bounded convex
bodies with nonempty interiors are homeomorphic. We apply it to the
coordinate polytope of a simplex and the unit cube.
-/

set_option autoImplicit false

open scoped unitInterval Topology

namespace FairDivision.Topology

open Set


/-- The generic convex-body ingredient for identifying two boundary sphere
models. -/
noncomputable def convexFrontierHomeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t : Set E}
    (hsc : Convex ℝ s) (hsne : (interior s).Nonempty) (hsb : Bornology.IsBounded s)
    (htc : Convex ℝ t) (htne : (interior t).Nonempty) (htb : Bornology.IsBounded t) :
    frontier s ≃ₜ frontier t := by
  let hw := exists_homeomorph_image_eq hsc hsne
      (NormedSpace.isVonNBounded_of_isBounded _ hsb)
      htc htne (NormedSpace.isVonNBounded_of_isBounded _ htb)
  let h := Classical.choose hw
  have hfrontier := (Classical.choose_spec hw).2.2
  apply Homeomorph.subtype h
  intro x
  constructor
  · intro hx
    rw [← hfrontier]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hfrontier] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact h.injective hxy ▸ hy

end FairDivision.Topology

namespace FairDivision.Topology


end FairDivision.Topology

namespace FairDivision.Topology


/-- Convex gauge rescaling identifies the two finite polytope frontiers. -/
noncomputable def finiteSimplexCubeFrontierHomeomorph (n : ℕ) :
    frontier (finiteSimplexPolytope n) ≃ₜ frontier (finiteUnitCube n) :=
  convexFrontierHomeomorph
    (finiteSimplexPolytope_convex n)
    (finiteSimplexPolytope_interior_nonempty n)
    (finiteSimplexPolytope_isBounded n)
    (finiteUnitCube_convex n)
    (finiteUnitCube_interior_nonempty n)
    (finiteUnitCube_isBounded n)

end FairDivision.Topology


namespace FairDivision.Topology


/-- The interior of a finite unit cube consists of its strict coordinate box. -/
theorem finiteUnitCube_interior (n : ℕ) :
    interior (finiteUnitCube n) =
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (0 : ℝ) 1) := by
  unfold finiteUnitCube
  rw [interior_pi_set (show (Set.univ : Set (Fin n)).Finite from Set.finite_univ)]
  simp only [interior_Icc]

/-- A point lies on the cube frontier exactly when some coordinate is an endpoint. -/
theorem mem_frontier_finiteUnitCube_iff (n : ℕ) (x : Fin n → ℝ) :
    x ∈ frontier (finiteUnitCube n) ↔
      x ∈ finiteUnitCube n ∧ ∃ i : Fin n, x i = 0 ∨ x i = 1 := by
  rw [(finiteUnitCube_isClosed n).frontier_eq]
  constructor
  · rintro ⟨hx, hnot⟩
    rw [finiteUnitCube_interior] at hnot
    have hnot' : ¬ ∀ i : Fin n, 0 < x i ∧ x i < 1 := by
      intro h
      apply hnot
      intro i _
      exact h i
    obtain ⟨i, hi⟩ := not_forall.mp hnot'
    have hxi : x i ∈ Set.Icc (0 : ℝ) 1 := hx i (Set.mem_univ i)
    refine ⟨hx, i, ?_⟩
    rcases not_and_or.mp hi with h0 | h1
    · exact Or.inl (le_antisymm (le_of_not_gt h0) hxi.1)
    · exact Or.inr (le_antisymm hxi.2 (le_of_not_gt h1))
  · rintro ⟨hx, i, hi⟩
    refine ⟨hx, ?_⟩
    rw [finiteUnitCube_interior]
    intro hint
    have hxi : x i ∈ Set.Ioo (0 : ℝ) 1 := hint i (Set.mem_univ i)
    rcases hxi with ⟨hlo, hhi⟩
    rcases hi with h0 | h1 <;> linarith

end FairDivision.Topology


namespace FairDivision.Topology

/-- The boundary-of-a-cube sphere used by operational connectivity is the
frontier of the coordinate cube. -/
noncomputable def cubeSphereFrontierHomeomorph (j : ℕ) :
    NerveConnectivity.CubeSphere j ≃ₜ frontier (finiteUnitCube (j + 1)) where
  toFun z := ⟨(fun i => (z.1 i : ℝ)), by
    apply (mem_frontier_finiteUnitCube_iff (j + 1) _).2
    constructor
    · intro i _
      exact (z.1 i).2
    · obtain ⟨i, hi⟩ := z.2
      refine ⟨i, ?_⟩
      rcases hi with h0 | h1
      · exact Or.inl (congrArg Subtype.val h0)
      · exact Or.inr (congrArg Subtype.val h1)⟩
  invFun x := ⟨(fun i => ⟨x.1 i,
      ((mem_frontier_finiteUnitCube_iff (j + 1) x.1).1 x.2).1 i (Set.mem_univ i)⟩), by
    obtain ⟨_, i, hi⟩ := (mem_frontier_finiteUnitCube_iff (j + 1) x.1).1 x.2
    refine ⟨i, ?_⟩
    rcases hi with h0 | h1
    · exact Or.inl (Subtype.ext h0)
    · exact Or.inr (Subtype.ext h1)⟩
  left_inv z := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    funext i
    rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_subtype_val : Continuous (fun x : I => (x : ℝ))).comp
      ((continuous_apply i).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact (continuous_apply i).comp continuous_subtype_val

end FairDivision.Topology


namespace FairDivision.Topology


/-- The coordinate sum as a continuous linear map. The positive number of
coordinates makes this map surjective and hence open. -/
def finiteCoordinateSumCLM (n : ℕ) :
    (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin (n + 1), ContinuousLinearMap.proj (R := ℝ) i

theorem finiteCoordinateSumCLM_apply (n : ℕ) (x : Fin (n + 1) → ℝ) :
    finiteCoordinateSumCLM n x = ∑ i : Fin (n + 1), x i := by
  simp [finiteCoordinateSumCLM]

theorem finiteCoordinateSumCLM_surjective (n : ℕ) :
    Function.Surjective (finiteCoordinateSumCLM n) := by
  intro y
  refine ⟨Pi.single (0 : Fin (n + 1)) y, ?_⟩
  rw [finiteCoordinateSumCLM_apply]
  simp

/-- At positive dimension, a simplex polytope point is interior exactly
when all barycentric coordinates, including the omitted last one, are positive. -/
theorem finiteSimplexPolytope_interior (n : ℕ) :
    interior (finiteSimplexPolytope (n + 1)) =
      finiteSimplexPolytopeOpen (n + 1) := by
  apply Set.Subset.antisymm
  · intro x hx
    constructor
    · intro i
      have hsubset : finiteSimplexPolytope (n + 1) ⊆
          (fun z : Fin (n + 1) → ℝ => z i) ⁻¹' Set.Ici (0 : ℝ) := by
        intro z hz
        exact hz.1 i
      have hmem := interior_mono hsubset hx
      have hopen : IsOpenMap (fun z : Fin (n + 1) → ℝ => z i) :=
        isOpenMap_eval i
      have hcont : Continuous (fun z : Fin (n + 1) → ℝ => z i) :=
        continuous_apply i
      rw [← hopen.preimage_interior_eq_interior_preimage
        hcont (Set.Ici (0 : ℝ))] at hmem
      simpa only [interior_Ici, Set.mem_preimage, Set.mem_Ioi] using hmem
    · have hsubset : finiteSimplexPolytope (n + 1) ⊆
          (finiteCoordinateSumCLM n) ⁻¹' Set.Iic (1 : ℝ) := by
        intro z hz
        change finiteCoordinateSumCLM n z ≤ 1
        simpa only [finiteCoordinateSumCLM_apply] using hz.2
      have hmem := interior_mono hsubset hx
      have hopen : IsOpenMap (finiteCoordinateSumCLM n) :=
        (finiteCoordinateSumCLM n).isOpenMap (finiteCoordinateSumCLM_surjective n)
      rw [← hopen.preimage_interior_eq_interior_preimage
        (finiteCoordinateSumCLM n).continuous (Set.Iic (1 : ℝ))] at hmem
      simpa only [interior_Iic, Set.mem_preimage, Set.mem_Iio,
        finiteCoordinateSumCLM_apply] using hmem
  · exact ((finiteSimplexPolytopeOpen_isOpen (n + 1)).subset_interior_iff.mpr
      (finiteSimplexPolytopeOpen_subset (n + 1)))

end FairDivision.Topology


namespace FairDivision.Topology

/-- The facets of the coordinate simplex are exactly its zero barycentric
coordinates, including the omitted last coordinate (the total-sum facet). -/
theorem mem_frontier_finiteSimplexPolytope_iff (n : ℕ)
    (x : Fin (n + 1) → ℝ) :
    x ∈ frontier (finiteSimplexPolytope (n + 1)) ↔
      x ∈ finiteSimplexPolytope (n + 1) ∧
        ((∃ i : Fin (n + 1), x i = 0) ∨
          (∑ i : Fin (n + 1), x i) = 1) := by
  rw [(finiteSimplexPolytope_isClosed (n + 1)).frontier_eq,
    finiteSimplexPolytope_interior]
  constructor
  · rintro ⟨hx, hnot⟩
    change ¬ ((∀ i : Fin (n + 1), 0 < x i) ∧
      (∑ i : Fin (n + 1), x i) < 1) at hnot
    by_cases hzero : ∃ i : Fin (n + 1), x i = 0
    · exact ⟨hx, Or.inl hzero⟩
    have hpos : ∀ i : Fin (n + 1), 0 < x i := by
      intro i
      rcases lt_or_eq_of_le (hx.1 i) with hlt | heq
      · exact hlt
      · exact False.elim (hzero ⟨i, heq.symm⟩)
    have hsum : (∑ i : Fin (n + 1), x i) = 1 := by
      rcases lt_or_eq_of_le hx.2 with hlt | heq
      · exact False.elim (hnot ⟨hpos, hlt⟩)
      · exact heq
    exact ⟨hx, Or.inr hsum⟩
  · rintro ⟨hx, hbdry⟩
    refine ⟨hx, ?_⟩
    change ¬ ((∀ i : Fin (n + 1), 0 < x i) ∧
      (∑ i : Fin (n + 1), x i) < 1)
    rintro ⟨hpos, hsum⟩
    rcases hbdry with ⟨i, hi⟩ | hi
    · linarith [hpos i]
    · linarith

end FairDivision.Topology


namespace FairDivision.Topology


end FairDivision.Topology


namespace FairDivision.Topology

/-- The boundary of a standard `(j+1)`-simplex, described without any
orientation or choice of a distinguished vertex. -/
abbrev finiteStandardSimplexBoundary (j : ℕ) :=
  {x : stdSimplex ℝ (Fin (j + 2)) // ∃ i : Fin (j + 2), x.1 i = 0}

/-- Omitting the last barycentric coordinate carries the zero-coordinate
simplex boundary exactly to the frontier of the coordinate simplex polytope. -/
theorem finiteStandardSimplex_boundary_iff_frontier (j : ℕ)
    (x : stdSimplex ℝ (Fin (j + 2))) :
    (∃ i : Fin (j + 2), x.1 i = 0) ↔
      (stdSimplexPolytopeHomeomorph (j + 1) x).1 ∈
        frontier (finiteSimplexPolytope (j + 1)) := by
  constructor
  · rintro ⟨i, hi⟩
    apply (mem_frontier_finiteSimplexPolytope_iff j _).2
    refine ⟨(stdSimplexPolytopeHomeomorph (j + 1) x).2, ?_⟩
    cases i using Fin.lastCases with
    | last =>
        right
        change (∑ i : Fin (j + 1), x.1 (Fin.castSucc i)) = 1
        have hsum := x.2.2
        rw [Fin.sum_univ_castSucc] at hsum
        linarith
    | cast i =>
        left
        exact ⟨i, hi⟩
  · intro hx
    obtain ⟨_, hfacet⟩ := (mem_frontier_finiteSimplexPolytope_iff j _).1 hx
    rcases hfacet with ⟨i, hi⟩ | hsum
    · exact ⟨Fin.castSucc i, hi⟩
    · refine ⟨Fin.last (j + 1), ?_⟩
      change (∑ i : Fin (j + 1), x.1 (Fin.castSucc i)) = 1 at hsum
      have htotal := x.2.2
      rw [Fin.sum_univ_castSucc] at htotal
      linarith

/-- The frontier as a nested subtype of the polytope is homeomorphic to
its ordinary ambient-space subtype. -/
noncomputable def finiteSimplexFrontierSubtypeHomeomorph (n : ℕ) :
    {y : finiteSimplexPolytope n // y.1 ∈ frontier (finiteSimplexPolytope n)} ≃ₜ
      frontier (finiteSimplexPolytope n) where
  toFun y := ⟨y.1.1, y.2⟩
  invFun x := ⟨⟨x.1, by
    simpa only [(finiteSimplexPolytope_isClosed n).closure_eq] using
      (frontier_subset_closure x.2)⟩, x.2⟩
  left_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val

/-- The zero-coordinate boundary of a standard simplex is the frontier of
the corresponding full-dimensional simplex polytope. -/
noncomputable def finiteStandardSimplexFrontierHomeomorph (j : ℕ) :
    finiteStandardSimplexBoundary j ≃ₜ
      frontier (finiteSimplexPolytope (j + 1)) :=
  (Homeomorph.subtype (stdSimplexPolytopeHomeomorph (j + 1))
    (finiteStandardSimplex_boundary_iff_frontier j)).trans
      (finiteSimplexFrontierSubtypeHomeomorph (j + 1))

/-- The attaching boundary of a finite simplex is homeomorphic to the
cube-boundary sphere used by operational connectivity. -/
noncomputable def finiteSimplexBoundaryCubeSphereHomeomorph (j : ℕ) :
    finiteStandardSimplexBoundary j ≃ₜ
      NerveConnectivity.CubeSphere j :=
  (finiteStandardSimplexFrontierHomeomorph j).trans
    ((finiteSimplexCubeFrontierHomeomorph (j + 1)).trans
      (cubeSphereFrontierHomeomorph j).symm)

end FairDivision.Topology
