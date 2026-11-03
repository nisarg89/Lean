import FairDivision.Topology.RegularTranslation

/-!
# The reduced regular representation sphere

Coordinates are real numbers indexed by the positions, constrained to sum to
zero and to have sum of squares one. This gives a concrete unit sphere in the
codimension-one representation used in the prime-power zero argument.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

/-- The unit sphere in the centered real coordinate hyperplane. -/
def ReducedSphere (n : ℕ) :=
  {z : Fin n → ℝ // (∑ i : Fin n, z i) = 0 ∧
    (∑ i : Fin n, (z i) ^ 2) = 1}

instance (n : ℕ) : TopologicalSpace (ReducedSphere n) := inferInstanceAs
  (TopologicalSpace {z : Fin n → ℝ // (∑ i : Fin n, z i) = 0 ∧
    (∑ i : Fin n, (z i) ^ 2) = 1})

/-- Relabel coordinates of a centered unit vector. -/
def relabelReducedSphere {n : ℕ} (σ : Equiv.Perm (Fin n))
    (z : ReducedSphere n) : ReducedSphere n := by
  refine ⟨fun i => z.1 (σ.symm i), ?_⟩
  constructor
  · simpa using (Equiv.sum_comp σ.symm (fun i : Fin n => z.1 i)).trans z.2.1
  · simpa using
      (Equiv.sum_comp σ.symm (fun i : Fin n => (z.1 i) ^ 2)).trans z.2.2

@[simp] theorem relabelReducedSphere_apply {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (z : ReducedSphere n) (i : Fin n) :
    (relabelReducedSphere σ z).1 i = z.1 (σ.symm i) := rfl

/-- A reduced unit vector cannot be fixed by all translations of a regular
p-torus position action. -/
theorem pTorus_reducedSphere_no_common_fixed
    (p r : ℕ) [NeZero p] (z : ReducedSphere (p ^ r))
    (hfixed : ∀ g : Fin r → ZMod p,
      relabelReducedSphere (pTorusPositionPerm p r g) z = z) : False := by
  have hcoordinate : ∀ g : Fin r → ZMod p, ∀ i : Fin (p ^ r),
      z.1 (pTorusPositionPerm p r g i) = z.1 i := by
    intro g i
    have h := congrArg
      (fun y : ReducedSphere (p ^ r) => y.1 (pTorusPositionPerm p r g i))
      (hfixed g)
    simpa [relabelReducedSphere] using h.symm
  have hzero : ∀ i : Fin (p ^ r), z.1 i = 0 :=
    centered_regular_fixed_zero (pTorusPositionEquiv p r) z.1 z.2.1
      hcoordinate
  have hsq : (∑ i : Fin (p ^ r), (z.1 i) ^ 2) = 0 := by
    simp [hzero]
  exact one_ne_zero (z.2.2.symm.trans hsq)

end FairDivision.Topology.Volovikov
