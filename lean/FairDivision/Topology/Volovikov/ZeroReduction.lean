import FairDivision.Topology.Volovikov.Equivariance

/-!
# Reduction of equivariant zeros to a sphere obstruction

If an equivariant centered score map had no zero, coordinatewise
normalization would give a continuous equivariant map to the reduced sphere.
This lemma packages that analytic reduction. Its `hnoSphereMap` argument is a
real topological obligation, not a claim proved here.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

/-- A no-map theorem for the reduced sphere forces a zero of every continuous
centered equivariant score map. The action is passed explicitly so this lemma
is reusable with any concrete group action and any connectivity formulation. -/
theorem zero_of_reducedSphere_obstruction
    {G X : Type*} {n : ℕ} [TopologicalSpace X]
    (act : G → X → X) (perm : G → Equiv.Perm (Fin n))
    (score : X → Fin n → ℝ)
    (hcontinuous : Continuous score)
    (hcenter : ∀ x : X, (∑ i : Fin n, score x i) = 0)
    (hequiv : ∀ (g : G) (x : X) (i : Fin n),
      score (act g x) (perm g i) = score x i)
    (hnoSphereMap : ∀ F : X → ReducedSphere n,
      Continuous F →
      (∀ (g : G) (x : X),
        F (act g x) = relabelReducedSphere (perm g) (F x)) → False) :
    ∃ x : X, score x = 0 := by
  by_contra hnozero
  have hnonzero : ∀ x : X, score x ≠ 0 := by
    intro x hx
    exact hnozero ⟨x, hx⟩
  let nz : X → CenteredNonzero n :=
    fun x => ⟨score x, hcenter x, hnonzero x⟩
  have hnz : Continuous nz := by
    apply Continuous.subtype_mk
    exact hcontinuous
  let F : X → ReducedSphere n := fun x => normalizeCentered (nz x)
  have hFcontinuous : Continuous F :=
    normalizeCentered_continuous.comp hnz
  have hFequiv : ∀ (g : G) (x : X),
      F (act g x) = relabelReducedSphere (perm g) (F x) := by
    intro g x
    have hnzEq : nz (act g x) = relabelCenteredNonzero (perm g) (nz x) := by
      apply Subtype.ext
      funext i
      have hi := hequiv g x ((perm g).symm i)
      simpa [nz, relabelCenteredNonzero] using hi
    change normalizeCentered (nz (act g x)) =
      relabelReducedSphere (perm g) (normalizeCentered (nz x))
    rw [hnzEq, normalizeCentered_relabel]
  exact hnoSphereMap F hFcontinuous hFequiv

end FairDivision.Topology.Volovikov
