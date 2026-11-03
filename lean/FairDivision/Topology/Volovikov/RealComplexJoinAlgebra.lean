import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.UnitInterval

/-!
# Real-to-complex doubling algebra

Two nonzero real vectors give a nonzero complex vector at every join
parameter: the first enters the real part, and the second the imaginary
part. The same formula preserves the zero-sum regular representation.
-/

set_option autoImplicit false

open scoped unitInterval

namespace FairDivision.Topology.Volovikov

/-- The coordinate formula for the real-to-complex join map. -/
def complexJoinVector {G : Type*} (t : I) (u v : G → ℝ) : G → ℂ :=
  fun g => (((1 - (t : ℝ)) * u g : ℝ) : ℂ) +
    Complex.I * (((t : ℝ) * v g : ℝ) : ℂ)

@[simp] theorem complexJoinVector_zero {G : Type*} (u v : G → ℝ) :
    complexJoinVector (0 : I) u v = fun g => (u g : ℂ) := by
  funext g
  simp [complexJoinVector]

@[simp] theorem complexJoinVector_one {G : Type*} (u v : G → ℝ) :
    complexJoinVector (1 : I) u v = fun g => Complex.I * (v g : ℂ) := by
  funext g
  simp [complexJoinVector]

/-- At least one of the real and imaginary parts is nonzero. -/
theorem complexJoinVector_ne_zero {G : Type*}
    (t : I) (u v : G → ℝ) (hu : u ≠ 0) (hv : v ≠ 0) :
    complexJoinVector t u v ≠ 0 := by
  classical
  by_cases ht : (t : ℝ) = 0
  · intro hzero
    apply hu
    funext g
    have hg := congrFun hzero g
    have hvalue : ((u g : ℝ) : ℂ) = 0 := by
      simpa [complexJoinVector, ht] using hg
    exact_mod_cast hvalue
  · obtain ⟨g, hg⟩ : ∃ g, v g ≠ 0 := by
      by_contra h
      push Not at h
      apply hv
      funext g
      exact h g
    intro hzero
    have him := congrArg Complex.im (congrFun hzero g)
    have hprod : (t : ℝ) * v g = 0 := by
      simpa [complexJoinVector, Complex.I_mul_im] using him
    rcases mul_eq_zero.mp hprod with h | h
    · exact ht h
    · exact hg h

/-- The join formula remains in the complex zero-sum subspace. -/
theorem complexJoinVector_sum_zero {G : Type*} [Fintype G]
    (t : I) (u v : G → ℝ)
    (hu : ∑ g, u g = 0) (hv : ∑ g, v g = 0) :
    ∑ g, complexJoinVector t u v g = 0 := by
  classical
  simp only [complexJoinVector, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Complex.ofReal_sum, hu, hv, Complex.ofReal_zero, mul_zero, add_zero]

end FairDivision.Topology.Volovikov
