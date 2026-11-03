import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.GaugeRescale

/-!
# The affine hyperplane of a finite simplex

A simplex face has empty interior in its ambient coordinate space. To apply
Mathlib's convex-body-to-ball homeomorphism in the virtual-valuation proof,
we first translate the face into the linear space of coordinate vectors
whose sum is zero. The center of the translated simplex is the origin.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open scoped BigOperators

/-- The linear hyperplane parallel to a finite probability simplex. -/
def simplexZeroSum (V : Type*) [Fintype V] : Submodule ℝ (V → ℝ) where
  carrier := {z | ∑ v, z v = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Pi.add_apply, Finset.sum_add_distrib]
    rw [hx, hy]
    simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [hx]
    simp

@[simp] theorem mem_simplexZeroSum_iff {V : Type*} [Fintype V]
    (z : V → ℝ) : z ∈ simplexZeroSum V ↔ ∑ v, z v = 0 := Iff.rfl

/-- The uniform barycentric coordinate of a nonempty finite simplex. -/
noncomputable def simplexBarycentricCoordinate (V : Type*) [Fintype V] : ℝ :=
  (Fintype.card V : ℝ)⁻¹

/-- The simplex translated so its barycenter is zero. Its ambient normed
space is the sum-zero submodule, so it has nonempty interior there. -/
def centeredSimplex (V : Type*) [Fintype V] : Set (simplexZeroSum V) :=
  {z | ∀ v : V, -simplexBarycentricCoordinate V ≤ z.1 v}

theorem simplexBarycentricCoordinate_pos
    (V : Type*) [Fintype V] [Nonempty V] :
    0 < simplexBarycentricCoordinate V := by
  have hcard : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos
  exact inv_pos.mpr hcard

theorem zero_mem_centeredSimplex
    (V : Type*) [Fintype V] [Nonempty V] :
    (0 : simplexZeroSum V) ∈ centeredSimplex V := by
  intro v
  have hb := simplexBarycentricCoordinate_pos V
  simpa [centeredSimplex] using (neg_nonpos.mpr hb.le)

/-- The translated simplex is closed in its sum-zero ambient space. -/
theorem centeredSimplex_isClosed (V : Type*) [Fintype V] :
    IsClosed (centeredSimplex V) := by
  have hEq : centeredSimplex V =
      ⋂ v : V, {z : simplexZeroSum V |
        -simplexBarycentricCoordinate V ≤ z.1 v} := by
    ext z
    simp [centeredSimplex]
  rw [hEq]
  apply isClosed_iInter
  intro v
  exact isClosed_Ici.preimage
    ((continuous_apply v).comp continuous_subtype_val)

/-- The translated simplex is convex in the sum-zero space. -/
theorem centeredSimplex_convex (V : Type*) [Fintype V] :
    Convex ℝ (centeredSimplex V) := by
  intro x hx y hy a b ha hb hab
  intro v
  change -simplexBarycentricCoordinate V ≤
    a * x.1 v + b * y.1 v
  calc
    -simplexBarycentricCoordinate V =
        a * (-simplexBarycentricCoordinate V) +
          b * (-simplexBarycentricCoordinate V) := by
      rw [← add_mul, hab, one_mul]
    _ ≤ a * x.1 v + b * y.1 v :=
      add_le_add
        (mul_le_mul_of_nonneg_left (hx v) ha)
        (mul_le_mul_of_nonneg_left (hy v) hb)

/-- The barycenter is an interior point once the simplex is regarded
inside its affine hyperplane. -/
theorem zero_mem_interior_centeredSimplex
    (V : Type*) [Fintype V] [Nonempty V] :
    (0 : simplexZeroSum V) ∈ interior (centeredSimplex V) := by
  let U : Set (simplexZeroSum V) :=
    ⋂ v : V, {z | -simplexBarycentricCoordinate V < z.1 v}
  have hOpen : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro v
    exact isOpen_Ioi.preimage
      ((continuous_apply v).comp continuous_subtype_val)
  have h0 : (0 : simplexZeroSum V) ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_setOf_eq]
    intro v
    have hb := simplexBarycentricCoordinate_pos V
    simpa using (neg_lt_zero.mpr hb)
  have hSub : U ⊆ centeredSimplex V := by
    intro z hz v
    exact le_of_lt (Set.mem_iInter.mp hz v)
  exact mem_interior.mpr ⟨U, hSub, hOpen, h0⟩

theorem centeredSimplex_interior_nonempty
    (V : Type*) [Fintype V] [Nonempty V] :
    (interior (centeredSimplex V)).Nonempty :=
  ⟨0, zero_mem_interior_centeredSimplex V⟩

end FairDivision.Topology
