import FairDivision.Topology.Volovikov.Normalization
import FairDivision.Topology.Volovikov.ContinuousAction

/-!
# Equivariance of normalization

Coordinate permutations preserve the centered nonzero locus and its radius.
Normalization therefore commutes with coordinate relabeling. These statements
are independent of any particular group acting on the coordinates.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

/-- Relabel coordinates of a nonzero centered vector. -/
def relabelCenteredNonzero {n : ℕ} (σ : Equiv.Perm (Fin n))
    (z : CenteredNonzero n) : CenteredNonzero n := by
  refine ⟨fun i => z.1 (σ.symm i), ?_⟩
  constructor
  · simpa using (Equiv.sum_comp σ.symm (fun i : Fin n => z.1 i)).trans z.2.1
  · intro hzero
    apply z.2.2
    funext i
    have hi := congrFun hzero (σ i)
    simpa using hi

@[simp] theorem relabelCenteredNonzero_apply {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (z : CenteredNonzero n) (i : Fin n) :
    (relabelCenteredNonzero σ z).1 i = z.1 (σ.symm i) := rfl

/-- Euclidean radius is invariant under a coordinate permutation. -/
theorem centeredRadius_relabel {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (z : Fin n → ℝ) :
    centeredRadius (fun i => z (σ.symm i)) = centeredRadius z := by
  unfold centeredRadius
  congr 1
  exact Equiv.sum_comp σ.symm (fun i : Fin n => (z i) ^ 2)

/-- Normalization commutes with coordinate relabeling. -/
theorem normalizeCentered_relabel {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (z : CenteredNonzero n) :
    normalizeCentered (relabelCenteredNonzero σ z) =
      relabelReducedSphere σ (normalizeCentered z) := by
  apply Subtype.ext
  funext i
  simp [normalizeCentered, relabelCenteredNonzero,
    relabelReducedSphere, centeredRadius_relabel]

/-- Relabeling is continuous on the centered nonzero locus. -/
theorem relabelCenteredNonzero_continuous {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    Continuous (relabelCenteredNonzero σ : CenteredNonzero n → CenteredNonzero n) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (continuous_apply (σ.symm i)).comp continuous_subtype_val

end FairDivision.Topology.Volovikov
