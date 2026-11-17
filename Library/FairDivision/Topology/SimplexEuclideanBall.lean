import FairDivision.Topology.SimplexAffineHyperplaneRealization
import FairDivision.Topology.SphericalCapBasic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# A Euclidean ball model of a finite simplex with its exact boundary

The existing affine-hyperplane model has the coordinate supremum norm.
Spherical-cap geometry needs an inner-product norm. Transport the same
centered convex body to its Euclidean sum-zero hyperplane before applying
Mathlib's gauge homeomorphism. This changes only the geometric model.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open scoped BigOperators

/-- The sum-zero hyperplane, with its genuine Euclidean inner product. -/
def euclideanSimplexZeroSum (V : Type*) [Fintype V] : Submodule ℝ (EuclideanSpace ℝ V) :=
  (simplexZeroSum V).comap (WithLp.linearEquiv 2 ℝ (V → ℝ)).toLinearMap

/-- The coordinate change preserves vectors and changes their normed model. -/
noncomputable def euclideanSimplexZeroSumEquiv (V : Type*) [Fintype V] :
    euclideanSimplexZeroSum V ≃L[ℝ] simplexZeroSum V := by
  let e := WithLp.linearEquiv 2 ℝ (V → ℝ)
  let l : euclideanSimplexZeroSum V ≃ₗ[ℝ] simplexZeroSum V :=
    {toFun := fun z => ⟨e z.1,z.2⟩
     invFun := fun z => ⟨e.symm z.1,by
       change e (e.symm z.1) ∈ simplexZeroSum V
       rw [e.apply_symm_apply]
       exact z.2⟩
     left_inv := by intro z; apply Subtype.ext; exact e.symm_apply_apply z.1
     right_inv := by intro z; apply Subtype.ext; exact e.apply_symm_apply z.1
     map_add' := by intro x y; apply Subtype.ext; exact e.map_add x.1 y.1
     map_smul' := by intro c z; apply Subtype.ext; exact e.map_smul c z.1}
  exact l.toContinuousLinearEquiv

/-- The same centered convex body viewed in its Euclidean hyperplane. -/
def euclideanCenteredSimplex (V : Type*) [Fintype V] : Set (euclideanSimplexZeroSum V) :=
  (euclideanSimplexZeroSumEquiv V) ⁻¹' centeredSimplex V

theorem euclideanCenteredSimplex_convex (V : Type*) [Fintype V] :
    Convex ℝ (euclideanCenteredSimplex V) :=
  (centeredSimplex_convex V).linear_preimage (euclideanSimplexZeroSumEquiv V).toLinearMap

theorem euclideanCenteredSimplex_isClosed (V : Type*) [Fintype V] :
    IsClosed (euclideanCenteredSimplex V) :=
  (centeredSimplex_isClosed V).preimage (euclideanSimplexZeroSumEquiv V).continuous

theorem euclideanCenteredSimplex_interior_nonempty (V : Type*) [Fintype V] [Nonempty V] :
    (interior (euclideanCenteredSimplex V)).Nonempty := by
  refine ⟨0,?_⟩
  change (0 : euclideanSimplexZeroSum V) ∈ interior
    ((euclideanSimplexZeroSumEquiv V).toHomeomorph ⁻¹' centeredSimplex V)
  rw [←(euclideanSimplexZeroSumEquiv V).toHomeomorph.preimage_interior]
  change euclideanSimplexZeroSumEquiv V 0 ∈ interior (centeredSimplex V)
  simpa only [map_zero] using zero_mem_interior_centeredSimplex V

theorem euclideanCenteredSimplex_isBounded (V : Type*) [Fintype V] [Nonempty V] :
    Bornology.IsBounded (euclideanCenteredSimplex V) := by
  have hCompact : IsCompact (centeredSimplex V) :=
    Metric.isCompact_of_isClosed_isBounded (centeredSimplex_isClosed V) (centeredSimplex_isBounded V)
  have hImage : (euclideanSimplexZeroSumEquiv V).symm '' centeredSimplex V=
      euclideanCenteredSimplex V := by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa [euclideanCenteredSimplex] using hy
    · intro hz
      exact ⟨euclideanSimplexZeroSumEquiv V z,hz,
        (euclideanSimplexZeroSumEquiv V).symm_apply_apply z⟩
  rw [←hImage]
  exact (hCompact.image (euclideanSimplexZeroSumEquiv V).symm.continuous).isBounded

/-- Choose a single ambient identification for every output coordinate. -/
noncomputable def simplexEuclideanGauge (V : Type*) [Fintype V] [Nonempty V] :
    euclideanSimplexZeroSum V ≃ₜ euclideanSimplexZeroSum V :=
  Classical.choose (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (euclideanCenteredSimplex_convex V) (euclideanCenteredSimplex_interior_nonempty V)
    (euclideanCenteredSimplex_isBounded V))

theorem simplexEuclideanGauge_images (V : Type*) [Fintype V] [Nonempty V] :
    simplexEuclideanGauge V '' euclideanCenteredSimplex V=Metric.closedBall 0 1 ∧
    simplexEuclideanGauge V '' frontier (euclideanCenteredSimplex V)=Metric.sphere 0 1 := by
  have h := Classical.choose_spec (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (euclideanCenteredSimplex_convex V) (euclideanCenteredSimplex_interior_nonempty V)
    (euclideanCenteredSimplex_isBounded V))
  simpa only [(euclideanCenteredSimplex_isClosed V).closure_eq,simplexEuclideanGauge] using h.2

private theorem gauge_mem_ball_iff (V : Type*) [Fintype V] [Nonempty V]
    (z : euclideanSimplexZeroSum V) :
    ‖simplexEuclideanGauge V z‖≤1 ↔ z∈euclideanCenteredSimplex V := by
  have h := (simplexEuclideanGauge_images V).1
  constructor
  · intro hz
    have hImage : simplexEuclideanGauge V z∈simplexEuclideanGauge V '' euclideanCenteredSimplex V := by
      rw [h]
      simpa using hz
    obtain ⟨w,hw,hwz⟩ := hImage
    exact (simplexEuclideanGauge V).injective hwz ▸ hw
  · intro hz
    have hImage := Set.mem_image_of_mem (simplexEuclideanGauge V) hz
    rw [h] at hImage
    simpa using hImage

/-- Probability simplex and Euclidean closed ball, with one fixed model
shared by all agent coordinates. -/
noncomputable def simplexEuclideanBallHomeomorph (V : Type*) [Fintype V] [Nonempty V] :
    stdSimplex ℝ V ≃ₜ ClosedUnitBall (euclideanSimplexZeroSum V) := by
  let e := euclideanSimplexZeroSumEquiv V
  let toEuclidean : centeredSimplex V ≃ₜ euclideanCenteredSimplex V :=
    e.symm.toHomeomorph.subtype (fun z => by
      change z ∈ centeredSimplex V ↔ e (e.symm z) ∈ centeredSimplex V
      rw [e.apply_symm_apply])
  let gauge : euclideanCenteredSimplex V ≃ₜ ClosedUnitBall (euclideanSimplexZeroSum V) :=
    (simplexEuclideanGauge V).subtype (fun z => (gauge_mem_ball_iff V z).symm)
  exact (simplexCenteredHomeomorph V).trans (toEuclidean.trans gauge)

/-- Exact boundary match needed to preserve all previously defined face
values. The ambient frontier is relative to the sum-zero hyperplane. -/
theorem simplexEuclideanBallHomeomorph_boundary_iff (V : Type*)
    [Fintype V] [Nonempty V] [Nontrivial V] (x : stdSimplex ℝ V) :
    ‖(simplexEuclideanBallHomeomorph V x : euclideanSimplexZeroSum V)‖=1 ↔
      ∃ v : V,x.1 v=0 := by
  let z := (euclideanSimplexZeroSumEquiv V).symm (simplexCenteredHomeomorph V x).1
  have hFrontier : simplexEuclideanGauge V z∈Metric.sphere 0 1 ↔
      z∈frontier (euclideanCenteredSimplex V) := by
    rw [←(simplexEuclideanGauge_images V).2]
    constructor
    · rintro ⟨w,hw,hwz⟩
      exact (simplexEuclideanGauge V).injective hwz ▸ hw
    · exact Set.mem_image_of_mem _
  have hCoordinate : z∈frontier (euclideanCenteredSimplex V) ↔
      (simplexCenteredHomeomorph V x).1∈frontier (centeredSimplex V) := by
    change z ∈ frontier
      ((euclideanSimplexZeroSumEquiv V).toHomeomorph ⁻¹' centeredSimplex V) ↔ _
    rw [←(euclideanSimplexZeroSumEquiv V).toHomeomorph.preimage_frontier]
    change euclideanSimplexZeroSumEquiv V z ∈ frontier (centeredSimplex V) ↔ _
    dsimp only [z]
    rw [(euclideanSimplexZeroSumEquiv V).apply_symm_apply]
  exact (show ‖(simplexEuclideanBallHomeomorph V x : euclideanSimplexZeroSum V)‖=1 ↔
      simplexEuclideanGauge V z∈Metric.sphere 0 1 by
      change ‖simplexEuclideanGauge V z‖=1 ↔ _
      simp only [Metric.mem_sphere,dist_zero_right]).trans
    (hFrontier.trans (hCoordinate.trans (simplexCenteredHomeomorph_boundary_iff x)))

/-- The affine dimension is the number of vertices minus one. The proof is
ordinary rank-nullity for the coordinate-sum functional; no topological
obstruction is supplied as a premise. -/
theorem euclideanSimplexZeroSum_finrank (V : Type*) [Fintype V] [Nonempty V] :
    Module.finrank ℝ (euclideanSimplexZeroSum V)=Fintype.card V-1 := by
  classical
  let total : (V→ℝ) →ₗ[ℝ] ℝ :=
    {toFun := fun z=>∑v,z v
     map_add' := by intro x y; exact Finset.sum_add_distrib
     map_smul' := by intro c x; simp [Finset.mul_sum]}
  have hKer : total.ker=simplexZeroSum V := by
    ext z
    rfl
  have hSurj : Function.Surjective total := by
    intro t
    exact ⟨Pi.single (Classical.choice (inferInstance : Nonempty V)) t,by simp [total]⟩
  have hDim := total.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hSurj,finrank_top,
    CommSemiring.finrank_self,hKer,Module.finrank_fintype_fun_eq_card] at hDim
  have hModel := (euclideanSimplexZeroSumEquiv V).toLinearEquiv.finrank_eq
  omega

/-- A face of dimension at least two has the spherical connectivity needed
for continuity of the moving-cap maximum. -/
theorem euclideanSimplexZeroSum_one_lt_rank (V : Type*) [Fintype V] [Nonempty V]
    (hCard : 3≤Fintype.card V) : 1<Module.rank ℝ (euclideanSimplexZeroSum V) := by
  apply Module.one_lt_rank_of_one_lt_finrank
  rw [euclideanSimplexZeroSum_finrank]
  omega

/-- The boundary sphere is inhabited whenever the face has dimension at
least one. -/
theorem euclideanSimplexZeroSum_unitSphere_nonempty (V : Type*) [Fintype V] [Nonempty V]
    (hCard : 2≤Fintype.card V) : Nonempty (UnitSphere (euclideanSimplexZeroSum V)) := by
  have hDim : 0<Module.finrank ℝ (euclideanSimplexZeroSum V) := by
    rw [euclideanSimplexZeroSum_finrank]
    omega
  letI : Nontrivial (euclideanSimplexZeroSum V) := Module.nontrivial_of_finrank_pos hDim
  obtain ⟨y,hy⟩ := NormedSpace.sphere_nonempty (E:=euclideanSimplexZeroSum V)
    (x:=0) (r:=1) |>.mpr (by norm_num)
  exact ⟨⟨y,by simpa only [Metric.mem_sphere,dist_zero_right] using hy⟩⟩

/-- Restrict the fixed ball model to its exact boundary. All agent
coordinates use this single homeomorphism. -/
noncomputable def simplexBoundaryEuclideanSphereHomeomorph (V : Type*)
    [Fintype V] [Nonempty V] [Nontrivial V] :
    SimplexBoundary V ≃ₜ UnitSphere (euclideanSimplexZeroSum V) where
  toFun x := ⟨(simplexEuclideanBallHomeomorph V x.1).1,
    (simplexEuclideanBallHomeomorph_boundary_iff V x.1).mpr x.2⟩
  invFun y := ⟨(simplexEuclideanBallHomeomorph V).symm ⟨y.1,y.2.le⟩,
    (simplexEuclideanBallHomeomorph_boundary_iff V _).mp (by
      simpa only [Homeomorph.apply_symm_apply] using y.2)⟩
  left_inv x := by
    apply Subtype.ext
    exact (simplexEuclideanBallHomeomorph V).symm_apply_apply x.1
  right_inv y := by
    apply Subtype.ext
    change ((simplexEuclideanBallHomeomorph V)
      ((simplexEuclideanBallHomeomorph V).symm
        (⟨y.1,y.2.le⟩ : ClosedUnitBall (euclideanSimplexZeroSum V)))).1 = y.1
    exact congrArg (fun z : ClosedUnitBall (euclideanSimplexZeroSum V) => z.1)
      ((simplexEuclideanBallHomeomorph V).apply_symm_apply ⟨y.1,y.2.le⟩)
  continuous_toFun :=
    (continuous_subtype_val.comp
      ((simplexEuclideanBallHomeomorph V).continuous.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    ((simplexEuclideanBallHomeomorph V).symm.continuous.comp
      (continuous_subtype_val.subtype_mk (fun y=>y.2.le))).subtype_mk _

@[simp] theorem simplexBoundaryEuclideanSphereHomeomorph_apply_coe (V : Type*)
    [Fintype V] [Nonempty V] [Nontrivial V] (x : SimplexBoundary V) :
    (simplexBoundaryEuclideanSphereHomeomorph V x).1=
      (simplexEuclideanBallHomeomorph V x.1).1 := rfl

end FairDivision.Topology
