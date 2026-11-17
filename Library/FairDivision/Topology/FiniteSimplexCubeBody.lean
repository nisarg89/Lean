import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# A finite simplex and a cube as convex bodies

Neutral finite-dimensional geometry shared by the BF and FE certificates.
Mathlib's convex gauge rescaling identifies the full simplex body with a
unit cube. The boundary-sphere and connectivity results live in separate
modules, so importing this file does not pull in either certificate.
-/

set_option autoImplicit false

open scoped unitInterval Topology

namespace FairDivision.Topology

open Set

/-- The full-dimensional simplex polytope obtained by omitting the last
barycentric coordinate of `stdSimplex ℝ (Fin (n+1))`. -/
def finiteSimplexPolytope (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑ i : Fin n, x i) ≤ 1}

/-- The ordinary unit cube in a finite-dimensional real function space. -/
def finiteUnitCube (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)

/-- The finite unit cube is convex. -/
theorem finiteUnitCube_convex (n : ℕ) : Convex ℝ (finiteUnitCube n) := by
  unfold finiteUnitCube
  exact convex_pi (fun _ _ => convex_Icc (0 : ℝ) 1)

/-- The finite unit cube is bounded. -/
theorem finiteUnitCube_isBounded (n : ℕ) :
    Bornology.IsBounded (finiteUnitCube n) := by
  unfold finiteUnitCube
  exact Bornology.IsBounded.pi (fun _ => Metric.isBounded_Icc 0 1)

/-- The finite unit cube contains a nonempty open coordinate box. -/
theorem finiteUnitCube_interior_nonempty (n : ℕ) :
    (interior (finiteUnitCube n)).Nonempty := by
  let x : Fin n → ℝ := fun _ => 1 / 2
  have hx : x ∈ Set.pi Set.univ (fun _ => Set.Ioo (0 : ℝ) 1) := by
    intro i _
    dsimp [x]
    constructor <;> norm_num
  have hopen : IsOpen (Set.pi Set.univ (fun _ => Set.Ioo (0 : ℝ) 1)) :=
    isOpen_set_pi (show (Set.univ : Set (Fin n)).Finite from Set.finite_univ)
      (fun _ _ => isOpen_Ioo)
  have hsubset : Set.pi Set.univ (fun _ => Set.Ioo (0 : ℝ) 1) ⊆
      finiteUnitCube n := by
    intro y hy i hi
    exact ⟨(hy i hi).1.le, (hy i hi).2.le⟩
  exact ⟨x, (hopen.subset_interior_iff.mpr hsubset) hx⟩

/-- The simplex polytope is convex. -/
theorem finiteSimplexPolytope_convex (n : ℕ) :
    Convex ℝ (finiteSimplexPolytope n) := by
  intro x hx y hy a b ha hb hab
  change (∀ i, 0 ≤ (a • x + b • y) i) ∧
    (∑ i : Fin n, (a • x + b • y) i) ≤ 1
  constructor
  · intro i
    change 0 ≤ a * x i + b * y i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · have hsum : (∑ i : Fin n, (a • x + b • y) i) =
        a * (∑ i : Fin n, x i) + b * (∑ i : Fin n, y i) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hsum]
    calc
      a * (∑ i : Fin n, x i) + b * (∑ i : Fin n, y i) ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
          (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = 1 := by nlinarith [hab]

/-- Every point of the simplex polytope lies in the unit cube. -/
theorem finiteSimplexPolytope_subset_cube (n : ℕ) :
    finiteSimplexPolytope n ⊆ finiteUnitCube n := by
  intro x hx i hi
  refine ⟨hx.1 i, ?_⟩
  have hcoord : x i ≤ ∑ j : Fin n, x j :=
    Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
  exact hcoord.trans hx.2

/-- The simplex polytope is bounded. -/
theorem finiteSimplexPolytope_isBounded (n : ℕ) :
    Bornology.IsBounded (finiteSimplexPolytope n) :=
  (finiteUnitCube_isBounded n).subset (finiteSimplexPolytope_subset_cube n)

/-- An explicit open part of the simplex polytope. -/
def finiteSimplexPolytopeOpen (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 < x i) ∧ (∑ i : Fin n, x i) < 1}

/-- The strict coordinate inequalities define an open set. -/
theorem finiteSimplexPolytopeOpen_isOpen (n : ℕ) :
    IsOpen (finiteSimplexPolytopeOpen n) := by
  have hcoord : IsOpen
      (Set.pi Set.univ (fun _ : Fin n => Set.Ioi (0 : ℝ))) :=
    isOpen_set_pi (show (Set.univ : Set (Fin n)).Finite from Set.finite_univ)
      (fun _ _ => isOpen_Ioi)
  have hsum : Continuous (fun x : Fin n → ℝ => ∑ i : Fin n, x i) :=
    continuous_finsetSum _ (fun i _ => continuous_apply i)
  have hsumOpen : IsOpen {x : Fin n → ℝ | (∑ i : Fin n, x i) < 1} :=
    isOpen_Iio.preimage hsum
  have heq : finiteSimplexPolytopeOpen n =
      (Set.pi Set.univ (fun _ : Fin n => Set.Ioi (0 : ℝ))) ∩
        {x : Fin n → ℝ | (∑ i : Fin n, x i) < 1} := by
    ext x
    simp [finiteSimplexPolytopeOpen, Set.mem_pi]
  rw [heq]
  exact hcoord.inter hsumOpen

/-- The strict inequalities imply the weak polytope inequalities. -/
theorem finiteSimplexPolytopeOpen_subset (n : ℕ) :
    finiteSimplexPolytopeOpen n ⊆ finiteSimplexPolytope n := by
  intro x hx
  exact ⟨fun i => (hx.1 i).le, hx.2.le⟩

/-- The simplex polytope has an interior point, including when `n = 0`. -/
theorem finiteSimplexPolytope_interior_nonempty (n : ℕ) :
    (interior (finiteSimplexPolytope n)).Nonempty := by
  let x : Fin n → ℝ := fun _ => 1 / ((n : ℝ) + 1)
  have hd : 0 < (n : ℝ) + 1 := by positivity
  have hx : x ∈ finiteSimplexPolytopeOpen n := by
    constructor
    · intro i
      exact one_div_pos.mpr hd
    · have hsum : (∑ i : Fin n, x i) =
          (n : ℝ) / ((n : ℝ) + 1) := by
        simp only [x, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        ring
      rw [hsum]
      exact (div_lt_one hd).2 (by linarith)
  exact ⟨x, ((finiteSimplexPolytopeOpen_isOpen n).subset_interior_iff.mpr
    (finiteSimplexPolytopeOpen_subset n)) hx⟩

/-- The finite unit cube is closed. -/
theorem finiteUnitCube_isClosed (n : ℕ) :
    IsClosed (finiteUnitCube n) := by
  unfold finiteUnitCube
  exact isClosed_set_pi (fun _ _ => isClosed_Icc)

/-- The coordinate simplex polytope is closed. -/
theorem finiteSimplexPolytope_isClosed (n : ℕ) :
    IsClosed (finiteSimplexPolytope n) := by
  have hcoord : IsClosed {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
    have heq : {x : Fin n → ℝ | ∀ i, 0 ≤ x i} =
        ⋂ i : Fin n, {x : Fin n → ℝ | 0 ≤ x i} := by
      ext x
      simp
    rw [heq]
    exact isClosed_iInter (fun i => isClosed_Ici.preimage (continuous_apply i))
  have hsum : Continuous (fun x : Fin n → ℝ => ∑ i : Fin n, x i) :=
    continuous_finsetSum _ (fun i _ => continuous_apply i)
  have hsumClosed : IsClosed {x : Fin n → ℝ | (∑ i : Fin n, x i) ≤ 1} :=
    isClosed_Iic.preimage hsum
  change IsClosed ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} ∩
    {x : Fin n → ℝ | (∑ i : Fin n, x i) ≤ 1})
  exact hcoord.inter hsumClosed

/-- Omitting the last barycentric coordinate identifies a standard simplex
with its full-dimensional coordinate polytope. -/
noncomputable def stdSimplexPolytopeHomeomorph (n : ℕ) :
    stdSimplex ℝ (Fin (n + 1)) ≃ₜ finiteSimplexPolytope n where
  toFun x := ⟨Fin.init x.1, by
    constructor
    · intro i
      exact x.2.1 (Fin.castSucc i)
    · have hsum :
          (∑ i : Fin n, x.1 (Fin.castSucc i)) + x.1 (Fin.last n) = 1 := by
        simpa only [Fin.sum_univ_castSucc] using x.2.2
      have hlast := x.2.1 (Fin.last n)
      change (∑ i : Fin n, x.1 (Fin.castSucc i)) ≤ 1
      linarith⟩
  invFun y := ⟨Fin.snoc y.1 (1 - ∑ i : Fin n, y.1 i), by
    constructor
    · intro i
      cases i using Fin.lastCases with
      | last =>
          simpa only [Fin.snoc_last] using sub_nonneg.mpr y.2.2
      | cast i =>
          simpa only [Fin.snoc_castSucc] using y.2.1 i
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      ring⟩
  left_inv x := by
    apply Subtype.ext
    have hsum :
        (∑ i : Fin n, x.1 (Fin.castSucc i)) + x.1 (Fin.last n) = 1 := by
      simpa only [Fin.sum_univ_castSucc] using x.2.2
    have hlast :
        1 - (∑ i : Fin n, Fin.init x.1 i) = x.1 (Fin.last n) := by
      change 1 - (∑ i : Fin n, x.1 (Fin.castSucc i)) = x.1 (Fin.last n)
      linarith
    change Fin.snoc (Fin.init x.1)
      (1 - ∑ i : Fin n, Fin.init x.1 i) = x.1
    rw [hlast]
    exact Fin.snoc_init_self x.1
  right_inv y := by
    apply Subtype.ext
    simp only [Fin.init_snoc]
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    change Continuous (fun x : stdSimplex ℝ (Fin (n + 1)) =>
      x.1 (Fin.castSucc i))
    exact (continuous_apply (Fin.castSucc i)).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    have hsum : Continuous (fun y : finiteSimplexPolytope n =>
        ∑ i : Fin n, y.1 i) :=
      continuous_finsetSum _ (fun i _ =>
        (continuous_apply i).comp continuous_subtype_val)
    cases i using Fin.lastCases with
    | last =>
        have hlast : Continuous (fun y : finiteSimplexPolytope n =>
            1 - ∑ i : Fin n, y.1 i) := by
          fun_prop
        simpa only [Fin.snoc_last] using hlast
    | cast i =>
        simpa only [Fin.snoc_castSucc, Function.comp_def] using
          ((continuous_apply i).comp continuous_subtype_val)

/-- An ambient homeomorphism carrying the finite simplex polytope to the
finite unit cube. -/
noncomputable def finiteSimplexCubeAmbientHomeomorph (n : ℕ) :
    (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
  Classical.choose (exists_homeomorph_image_eq
    (FairDivision.Topology.finiteSimplexPolytope_convex n)
    (FairDivision.Topology.finiteSimplexPolytope_interior_nonempty n)
    (NormedSpace.isVonNBounded_of_isBounded _
      (FairDivision.Topology.finiteSimplexPolytope_isBounded n))
    (FairDivision.Topology.finiteUnitCube_convex n)
    (FairDivision.Topology.finiteUnitCube_interior_nonempty n)
    (NormedSpace.isVonNBounded_of_isBounded _
      (FairDivision.Topology.finiteUnitCube_isBounded n)))

/-- Gauge rescaling carries the closed simplex body onto the closed cube. -/
theorem finiteSimplexCubeAmbient_image (n : ℕ) :
    finiteSimplexCubeAmbientHomeomorph n ''
      FairDivision.Topology.finiteSimplexPolytope n =
        FairDivision.Topology.finiteUnitCube n := by
  have h := (Classical.choose_spec (exists_homeomorph_image_eq
    (FairDivision.Topology.finiteSimplexPolytope_convex n)
    (FairDivision.Topology.finiteSimplexPolytope_interior_nonempty n)
    (NormedSpace.isVonNBounded_of_isBounded _
      (FairDivision.Topology.finiteSimplexPolytope_isBounded n))
    (FairDivision.Topology.finiteUnitCube_convex n)
    (FairDivision.Topology.finiteUnitCube_interior_nonempty n)
    (NormedSpace.isVonNBounded_of_isBounded _
      (FairDivision.Topology.finiteUnitCube_isBounded n)))).2.1
  simpa only [finiteSimplexCubeAmbientHomeomorph,
    (FairDivision.Topology.finiteSimplexPolytope_isClosed n).closure_eq,
    (FairDivision.Topology.finiteUnitCube_isClosed n).closure_eq] using h

/-- Homeomorphism between the closed simplex polytope and the closed cube. -/
noncomputable def finiteSimplexCubeBodyHomeomorph (n : ℕ) :
    FairDivision.Topology.finiteSimplexPolytope n ≃ₜ
      FairDivision.Topology.finiteUnitCube n := by
  let e := finiteSimplexCubeAmbientHomeomorph n
  have hiff (x : Fin n → ℝ) :
      x ∈ FairDivision.Topology.finiteSimplexPolytope n ↔
        e x ∈ FairDivision.Topology.finiteUnitCube n := by
    have himage := finiteSimplexCubeAmbient_image n
    constructor
    · intro hx
      rw [← himage]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← himage] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      exact e.injective hxy ▸ hy
  exact e.subtype hiff

/-- The standard simplex is homeomorphic, as a whole body, to a cube
of the same dimension. -/
noncomputable def standardSimplexCubeBodyHomeomorph (n : ℕ) :
    stdSimplex ℝ (Fin (n + 1)) ≃ₜ FairDivision.Topology.finiteUnitCube n :=
  (FairDivision.Topology.stdSimplexPolytopeHomeomorph n).trans
    (finiteSimplexCubeBodyHomeomorph n)

/-- The real-coordinate cube as a subtype is the product of unit intervals. -/
noncomputable def finiteUnitCubeBodyHomeomorph (n : ℕ) :
    FairDivision.Topology.finiteUnitCube n ≃ₜ I^ (Fin n) where
  toFun x := fun i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
  invFun q := ⟨fun i => (q i : ℝ), by
    intro i _
    exact (q i).2⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    rfl
  right_inv q := by
    funext i
    apply Subtype.ext
    rfl
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact (continuous_apply i).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact continuous_subtype_val.comp (continuous_apply i)

end FairDivision.Topology
